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

/* Altera - ALT_SPIM */

#ifndef __ALTERA_ALT_SPIM_H__
#define __ALTERA_ALT_SPIM_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : SPI Master Module - ALT_SPIM
 * SPI Master Module
 * 
 * Registers in the SPI Master module
 * 
 */
/*
 * Register : Control Register 0 - ctrlr0
 * 
 * This register controls the serial data transfer. It is impossible to write to
 * this register when the SPI Master is enabled. The SPI Master is enabled and
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
 *  [10]    | ???    | 0x0   | *UNDEFINED*          
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
 * logic, with the upper bits of the receive FIFO zero-padded. You must right-
 * justify transmit data before writing into the transmit FIFO. The transmit logic
 * ignores the upper unused bits when transmitting the data.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description                
 * :--------------------------------|:------|:----------------------------
 *  ALT_SPIM_CTLR0_DFS_E_WIDTH4BIT  | 0x3   | 4-bit serial data transfer 
 *  ALT_SPIM_CTLR0_DFS_E_WIDTH5BIT  | 0x4   | 5-bit serial data transfer 
 *  ALT_SPIM_CTLR0_DFS_E_WIDTH6BIT  | 0x5   | 6-bit serial data transfer 
 *  ALT_SPIM_CTLR0_DFS_E_WIDTH7BIT  | 0x6   | 7-bit serial data transfer 
 *  ALT_SPIM_CTLR0_DFS_E_WIDTH8BIT  | 0x7   | 8-bit serial data transfer 
 *  ALT_SPIM_CTLR0_DFS_E_WIDTH9BIT  | 0x8   | 9-bit serial data transfer 
 *  ALT_SPIM_CTLR0_DFS_E_WIDTH10BIT | 0x9   | 10-bit serial data transfer
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_DFS
 * 
 * 4-bit serial data transfer
 */
#define ALT_SPIM_CTLR0_DFS_E_WIDTH4BIT  0x3
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_DFS
 * 
 * 5-bit serial data transfer
 */
#define ALT_SPIM_CTLR0_DFS_E_WIDTH5BIT  0x4
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_DFS
 * 
 * 6-bit serial data transfer
 */
#define ALT_SPIM_CTLR0_DFS_E_WIDTH6BIT  0x5
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_DFS
 * 
 * 7-bit serial data transfer
 */
#define ALT_SPIM_CTLR0_DFS_E_WIDTH7BIT  0x6
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_DFS
 * 
 * 8-bit serial data transfer
 */
#define ALT_SPIM_CTLR0_DFS_E_WIDTH8BIT  0x7
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_DFS
 * 
 * 9-bit serial data transfer
 */
#define ALT_SPIM_CTLR0_DFS_E_WIDTH9BIT  0x8
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_DFS
 * 
 * 10-bit serial data transfer
 */
#define ALT_SPIM_CTLR0_DFS_E_WIDTH10BIT 0x9

/* The Least Significant Bit (LSB) position of the ALT_SPIM_CTLR0_DFS register field. */
#define ALT_SPIM_CTLR0_DFS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_CTLR0_DFS register field. */
#define ALT_SPIM_CTLR0_DFS_MSB        3
/* The width in bits of the ALT_SPIM_CTLR0_DFS register field. */
#define ALT_SPIM_CTLR0_DFS_WIDTH      4
/* The mask used to set the ALT_SPIM_CTLR0_DFS register field value. */
#define ALT_SPIM_CTLR0_DFS_SET_MSK    0x0000000f
/* The mask used to clear the ALT_SPIM_CTLR0_DFS register field value. */
#define ALT_SPIM_CTLR0_DFS_CLR_MSK    0xfffffff0
/* The reset value of the ALT_SPIM_CTLR0_DFS register field. */
#define ALT_SPIM_CTLR0_DFS_RESET      0x7
/* Extracts the ALT_SPIM_CTLR0_DFS field value from a register. */
#define ALT_SPIM_CTLR0_DFS_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_SPIM_CTLR0_DFS register field value suitable for setting the register. */
#define ALT_SPIM_CTLR0_DFS_SET(value) (((value) << 0) & 0x0000000f)

/*
 * Field : Frame Format - frf
 * 
 * Selects which serial protocol transfers the data.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description            
 * :----------------------------|:------|:------------------------
 *  ALT_SPIM_CTLR0_FRF_E_MOTSPI | 0x0   | Motorola SPI           
 *  ALT_SPIM_CTLR0_FRF_E_TISSP  | 0x1   | Texas Instruments  SSP 
 *  ALT_SPIM_CTLR0_FRF_E_NATMW  | 0x2   | National Semi Microwire
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_FRF
 * 
 * Motorola SPI
 */
#define ALT_SPIM_CTLR0_FRF_E_MOTSPI 0x0
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_FRF
 * 
 * Texas Instruments  SSP
 */
#define ALT_SPIM_CTLR0_FRF_E_TISSP  0x1
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_FRF
 * 
 * National Semi Microwire
 */
#define ALT_SPIM_CTLR0_FRF_E_NATMW  0x2

/* The Least Significant Bit (LSB) position of the ALT_SPIM_CTLR0_FRF register field. */
#define ALT_SPIM_CTLR0_FRF_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SPIM_CTLR0_FRF register field. */
#define ALT_SPIM_CTLR0_FRF_MSB        5
/* The width in bits of the ALT_SPIM_CTLR0_FRF register field. */
#define ALT_SPIM_CTLR0_FRF_WIDTH      2
/* The mask used to set the ALT_SPIM_CTLR0_FRF register field value. */
#define ALT_SPIM_CTLR0_FRF_SET_MSK    0x00000030
/* The mask used to clear the ALT_SPIM_CTLR0_FRF register field value. */
#define ALT_SPIM_CTLR0_FRF_CLR_MSK    0xffffffcf
/* The reset value of the ALT_SPIM_CTLR0_FRF register field. */
#define ALT_SPIM_CTLR0_FRF_RESET      0x0
/* Extracts the ALT_SPIM_CTLR0_FRF field value from a register. */
#define ALT_SPIM_CTLR0_FRF_GET(value) (((value) & 0x00000030) >> 4)
/* Produces a ALT_SPIM_CTLR0_FRF register field value suitable for setting the register. */
#define ALT_SPIM_CTLR0_FRF_SET(value) (((value) << 4) & 0x00000030)

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
 *  Enum                           | Value | Description                                     
 * :-------------------------------|:------|:-------------------------------------------------
 *  ALT_SPIM_CTLR0_SCPH_E_MIDBIT   | 0x0   | Serial clock toggles in middle of first data bit
 *  ALT_SPIM_CTLR0_SCPH_E_STARTBIT | 0x1   | Serial clock toggles at start of first data bit 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_SCPH
 * 
 * Serial clock toggles in middle of first data bit
 */
#define ALT_SPIM_CTLR0_SCPH_E_MIDBIT    0x0
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_SCPH
 * 
 * Serial clock toggles at start of first data bit
 */
#define ALT_SPIM_CTLR0_SCPH_E_STARTBIT  0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_CTLR0_SCPH register field. */
#define ALT_SPIM_CTLR0_SCPH_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_SPIM_CTLR0_SCPH register field. */
#define ALT_SPIM_CTLR0_SCPH_MSB        6
/* The width in bits of the ALT_SPIM_CTLR0_SCPH register field. */
#define ALT_SPIM_CTLR0_SCPH_WIDTH      1
/* The mask used to set the ALT_SPIM_CTLR0_SCPH register field value. */
#define ALT_SPIM_CTLR0_SCPH_SET_MSK    0x00000040
/* The mask used to clear the ALT_SPIM_CTLR0_SCPH register field value. */
#define ALT_SPIM_CTLR0_SCPH_CLR_MSK    0xffffffbf
/* The reset value of the ALT_SPIM_CTLR0_SCPH register field. */
#define ALT_SPIM_CTLR0_SCPH_RESET      0x0
/* Extracts the ALT_SPIM_CTLR0_SCPH field value from a register. */
#define ALT_SPIM_CTLR0_SCPH_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_SPIM_CTLR0_SCPH register field value suitable for setting the register. */
#define ALT_SPIM_CTLR0_SCPH_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Serial Clock Polarity - scpol
 * 
 * Valid when the frame format (FRF) is set to Motorola SPI. Used to select the
 * polarity of the inactive serial clock, which is held inactive when the SPI
 * Master is not actively transferring data on the serial bus.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                           
 * :---------------------------------|:------|:---------------------------------------
 *  ALT_SPIM_CTLR0_SCPOL_E_INACTLOW  | 0x0   | Inactive state of serial clock is low 
 *  ALT_SPIM_CTLR0_SCPOL_E_INACTHIGH | 0x1   | Inactive state of serial clock is high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_SCPOL
 * 
 * Inactive state of serial clock is low
 */
#define ALT_SPIM_CTLR0_SCPOL_E_INACTLOW     0x0
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_SCPOL
 * 
 * Inactive state of serial clock is high
 */
#define ALT_SPIM_CTLR0_SCPOL_E_INACTHIGH    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_CTLR0_SCPOL register field. */
#define ALT_SPIM_CTLR0_SCPOL_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_SPIM_CTLR0_SCPOL register field. */
#define ALT_SPIM_CTLR0_SCPOL_MSB        7
/* The width in bits of the ALT_SPIM_CTLR0_SCPOL register field. */
#define ALT_SPIM_CTLR0_SCPOL_WIDTH      1
/* The mask used to set the ALT_SPIM_CTLR0_SCPOL register field value. */
#define ALT_SPIM_CTLR0_SCPOL_SET_MSK    0x00000080
/* The mask used to clear the ALT_SPIM_CTLR0_SCPOL register field value. */
#define ALT_SPIM_CTLR0_SCPOL_CLR_MSK    0xffffff7f
/* The reset value of the ALT_SPIM_CTLR0_SCPOL register field. */
#define ALT_SPIM_CTLR0_SCPOL_RESET      0x0
/* Extracts the ALT_SPIM_CTLR0_SCPOL field value from a register. */
#define ALT_SPIM_CTLR0_SCPOL_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_SPIM_CTLR0_SCPOL register field value suitable for setting the register. */
#define ALT_SPIM_CTLR0_SCPOL_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Transfer Mode - tmod
 * 
 * Selects the mode of transfer for serial communication. This field does not
 * affect the transfer duplicity. Only indicates whether the receive or transmit
 * data are valid. In transmit-only mode, data received from the external device is
 * not valid and is not stored in the receive FIFO memory. It is overwritten on the
 * next transfer. In receive-only mode, transmitted data are not valid. After the
 * first write to the transmit FIFO, the same word is retransmitted for the
 * duration of the transfer. In transmit-and-receive mode, both transmit and
 * receive data are valid. The transfer continues until the transmit FIFO is empty.
 * Data received from the external device are stored into the receive FIFO memory,
 * where it can be accessed by the host processor.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description           
 * :-----------------------------|:------|:-----------------------
 *  ALT_SPIM_CTLR0_TMOD_E_TXRX   | 0x0   | Transmit & and Receive
 *  ALT_SPIM_CTLR0_TMOD_E_TXONLY | 0x1   | Transmit Only         
 *  ALT_SPIM_CTLR0_TMOD_E_RXONLY | 0x2   | Receive Only          
 *  ALT_SPIM_CTLR0_TMOD_E_EERD   | 0x3   | EEPROM Read           
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_TMOD
 * 
 * Transmit & and Receive
 */
#define ALT_SPIM_CTLR0_TMOD_E_TXRX      0x0
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_TMOD
 * 
 * Transmit Only
 */
#define ALT_SPIM_CTLR0_TMOD_E_TXONLY    0x1
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_TMOD
 * 
 * Receive Only
 */
#define ALT_SPIM_CTLR0_TMOD_E_RXONLY    0x2
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_TMOD
 * 
 * EEPROM Read
 */
#define ALT_SPIM_CTLR0_TMOD_E_EERD      0x3

/* The Least Significant Bit (LSB) position of the ALT_SPIM_CTLR0_TMOD register field. */
#define ALT_SPIM_CTLR0_TMOD_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_SPIM_CTLR0_TMOD register field. */
#define ALT_SPIM_CTLR0_TMOD_MSB        9
/* The width in bits of the ALT_SPIM_CTLR0_TMOD register field. */
#define ALT_SPIM_CTLR0_TMOD_WIDTH      2
/* The mask used to set the ALT_SPIM_CTLR0_TMOD register field value. */
#define ALT_SPIM_CTLR0_TMOD_SET_MSK    0x00000300
/* The mask used to clear the ALT_SPIM_CTLR0_TMOD register field value. */
#define ALT_SPIM_CTLR0_TMOD_CLR_MSK    0xfffffcff
/* The reset value of the ALT_SPIM_CTLR0_TMOD register field. */
#define ALT_SPIM_CTLR0_TMOD_RESET      0x0
/* Extracts the ALT_SPIM_CTLR0_TMOD field value from a register. */
#define ALT_SPIM_CTLR0_TMOD_GET(value) (((value) & 0x00000300) >> 8)
/* Produces a ALT_SPIM_CTLR0_TMOD register field value suitable for setting the register. */
#define ALT_SPIM_CTLR0_TMOD_SET(value) (((value) << 8) & 0x00000300)

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
 *  ALT_SPIM_CTLR0_SRL_E_NORMMOD | 0x0   | Normal Mode Operation
 *  ALT_SPIM_CTLR0_SRL_E_TESTMOD | 0x1   | Test Mode Operation  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_SRL
 * 
 * Normal Mode Operation
 */
#define ALT_SPIM_CTLR0_SRL_E_NORMMOD    0x0
/*
 * Enumerated value for register field ALT_SPIM_CTLR0_SRL
 * 
 * Test Mode Operation
 */
#define ALT_SPIM_CTLR0_SRL_E_TESTMOD    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_CTLR0_SRL register field. */
#define ALT_SPIM_CTLR0_SRL_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_SPIM_CTLR0_SRL register field. */
#define ALT_SPIM_CTLR0_SRL_MSB        11
/* The width in bits of the ALT_SPIM_CTLR0_SRL register field. */
#define ALT_SPIM_CTLR0_SRL_WIDTH      1
/* The mask used to set the ALT_SPIM_CTLR0_SRL register field value. */
#define ALT_SPIM_CTLR0_SRL_SET_MSK    0x00000800
/* The mask used to clear the ALT_SPIM_CTLR0_SRL register field value. */
#define ALT_SPIM_CTLR0_SRL_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_SPIM_CTLR0_SRL register field. */
#define ALT_SPIM_CTLR0_SRL_RESET      0x0
/* Extracts the ALT_SPIM_CTLR0_SRL field value from a register. */
#define ALT_SPIM_CTLR0_SRL_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_SPIM_CTLR0_SRL register field value suitable for setting the register. */
#define ALT_SPIM_CTLR0_SRL_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : Control Frame Size - cfs
 * 
 * Selects the length of the control word for the Microwire frame format. The
 * length (in bits) is the value of this field plus 1.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIM_CTLR0_CFS register field. */
#define ALT_SPIM_CTLR0_CFS_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_SPIM_CTLR0_CFS register field. */
#define ALT_SPIM_CTLR0_CFS_MSB        15
/* The width in bits of the ALT_SPIM_CTLR0_CFS register field. */
#define ALT_SPIM_CTLR0_CFS_WIDTH      4
/* The mask used to set the ALT_SPIM_CTLR0_CFS register field value. */
#define ALT_SPIM_CTLR0_CFS_SET_MSK    0x0000f000
/* The mask used to clear the ALT_SPIM_CTLR0_CFS register field value. */
#define ALT_SPIM_CTLR0_CFS_CLR_MSK    0xffff0fff
/* The reset value of the ALT_SPIM_CTLR0_CFS register field. */
#define ALT_SPIM_CTLR0_CFS_RESET      0x0
/* Extracts the ALT_SPIM_CTLR0_CFS field value from a register. */
#define ALT_SPIM_CTLR0_CFS_GET(value) (((value) & 0x0000f000) >> 12)
/* Produces a ALT_SPIM_CTLR0_CFS register field value suitable for setting the register. */
#define ALT_SPIM_CTLR0_CFS_SET(value) (((value) << 12) & 0x0000f000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_CTLR0.
 */
struct ALT_SPIM_CTLR0_s
{
    uint32_t  dfs   :  4;  /* Data Frame Size */
    uint32_t  frf   :  2;  /* Frame Format */
    uint32_t  scph  :  1;  /* Serial Clock Phase */
    uint32_t  scpol :  1;  /* Serial Clock Polarity */
    uint32_t  tmod  :  2;  /* Transfer Mode */
    uint32_t        :  1;  /* *UNDEFINED* */
    uint32_t  srl   :  1;  /* Shift Register Loop */
    uint32_t  cfs   :  4;  /* Control Frame Size */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_CTLR0. */
typedef volatile struct ALT_SPIM_CTLR0_s  ALT_SPIM_CTLR0_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_CTLR0 register from the beginning of the component. */
#define ALT_SPIM_CTLR0_OFST        0x0
/* The address of the ALT_SPIM_CTLR0 register. */
#define ALT_SPIM_CTLR0_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_CTLR0_OFST))

/*
 * Register : Control Register 1 - ctrlr1
 * 
 * Control register 1 controls the end of serial transfers when in receive-only
 * mode. It is impossible to write to this register when the SPI Master is
 * enabled.The SPI Master is enabled and disabled by writing to the SPIENR
 * register.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description          
 * :--------|:-------|:------|:----------------------
 *  [15:0]  | RW     | 0x0   | Number of Data Frames
 *  [31:16] | ???    | 0x0   | *UNDEFINED*          
 * 
 */
/*
 * Field : Number of Data Frames - ndf
 * 
 * When TMOD = 10 or TMOD =11, this register field sets the number of data frames
 * to be continuously received by the SPI Master. The SPI Master continues to
 * receive serial data until the number of data frames received is equal to this
 * register value plus 1, which enables you to receive up to 64 KB of data in a
 * continuous transfer.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIM_CTLR1_NDF register field. */
#define ALT_SPIM_CTLR1_NDF_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_CTLR1_NDF register field. */
#define ALT_SPIM_CTLR1_NDF_MSB        15
/* The width in bits of the ALT_SPIM_CTLR1_NDF register field. */
#define ALT_SPIM_CTLR1_NDF_WIDTH      16
/* The mask used to set the ALT_SPIM_CTLR1_NDF register field value. */
#define ALT_SPIM_CTLR1_NDF_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_SPIM_CTLR1_NDF register field value. */
#define ALT_SPIM_CTLR1_NDF_CLR_MSK    0xffff0000
/* The reset value of the ALT_SPIM_CTLR1_NDF register field. */
#define ALT_SPIM_CTLR1_NDF_RESET      0x0
/* Extracts the ALT_SPIM_CTLR1_NDF field value from a register. */
#define ALT_SPIM_CTLR1_NDF_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_SPIM_CTLR1_NDF register field value suitable for setting the register. */
#define ALT_SPIM_CTLR1_NDF_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_CTLR1.
 */
struct ALT_SPIM_CTLR1_s
{
    uint32_t  ndf : 16;  /* Number of Data Frames */
    uint32_t      : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_CTLR1. */
typedef volatile struct ALT_SPIM_CTLR1_s  ALT_SPIM_CTLR1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_CTLR1 register from the beginning of the component. */
#define ALT_SPIM_CTLR1_OFST        0x4
/* The address of the ALT_SPIM_CTLR1 register. */
#define ALT_SPIM_CTLR1_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_CTLR1_OFST))

/*
 * Register : Enable Register - spienr
 * 
 * Enables and Disables all SPI operations.
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
 * Enables and disables all SPI Master operations. When disabled, all serial
 * transfers are halted immediately. Transmit and receive FIFO buffers are cleared
 * when the device is disabled. It is impossible to program some of the SPI Master
 * control registers when enabled.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                        
 * :------------------------------|:------|:------------------------------------
 *  ALT_SPIM_SPIENR_SPI_EN_E_DISD | 0x0   | Disables serial transfer operations
 *  ALT_SPIM_SPIENR_SPI_EN_E_END  | 0x1   | Enables serial transfer operations 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_SPIENR_SPI_EN
 * 
 * Disables serial transfer operations
 */
#define ALT_SPIM_SPIENR_SPI_EN_E_DISD   0x0
/*
 * Enumerated value for register field ALT_SPIM_SPIENR_SPI_EN
 * 
 * Enables serial transfer operations
 */
#define ALT_SPIM_SPIENR_SPI_EN_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_SPIENR_SPI_EN register field. */
#define ALT_SPIM_SPIENR_SPI_EN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_SPIENR_SPI_EN register field. */
#define ALT_SPIM_SPIENR_SPI_EN_MSB        0
/* The width in bits of the ALT_SPIM_SPIENR_SPI_EN register field. */
#define ALT_SPIM_SPIENR_SPI_EN_WIDTH      1
/* The mask used to set the ALT_SPIM_SPIENR_SPI_EN register field value. */
#define ALT_SPIM_SPIENR_SPI_EN_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIM_SPIENR_SPI_EN register field value. */
#define ALT_SPIM_SPIENR_SPI_EN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIM_SPIENR_SPI_EN register field. */
#define ALT_SPIM_SPIENR_SPI_EN_RESET      0x0
/* Extracts the ALT_SPIM_SPIENR_SPI_EN field value from a register. */
#define ALT_SPIM_SPIENR_SPI_EN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIM_SPIENR_SPI_EN register field value suitable for setting the register. */
#define ALT_SPIM_SPIENR_SPI_EN_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_SPIENR.
 */
struct ALT_SPIM_SPIENR_s
{
    uint32_t  spi_en :  1;  /* Enable */
    uint32_t         : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_SPIENR. */
typedef volatile struct ALT_SPIM_SPIENR_s  ALT_SPIM_SPIENR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_SPIENR register from the beginning of the component. */
#define ALT_SPIM_SPIENR_OFST        0x8
/* The address of the ALT_SPIM_SPIENR register. */
#define ALT_SPIM_SPIENR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_SPIENR_OFST))

/*
 * Register : Microwire Control Register - mwcr
 * 
 * This register controls the direction of the data word for the half-duplex
 * Microwire serial protocol. It is impossible to write to this register when the
 * SPI Master is enabled. The SPI Master is enabled and disabled by writing to the
 * SPIENR register.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description            
 * :-------|:-------|:------|:------------------------
 *  [0]    | RW     | 0x0   | Microwire Transfer Mode
 *  [1]    | RW     | 0x0   | Microwire Control      
 *  [2]    | RW     | 0x0   | Microwire Handshaking  
 *  [31:3] | ???    | 0x0   | *UNDEFINED*            
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
 *  ALT_SPIM_MWCR_MWMOD_E_NONSEQ | 0x0   | non-sequential transfer
 *  ALT_SPIM_MWCR_MWMOD_E_SEQ    | 0x1   | sequential transfer    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_MWCR_MWMOD
 * 
 * non-sequential transfer
 */
#define ALT_SPIM_MWCR_MWMOD_E_NONSEQ    0x0
/*
 * Enumerated value for register field ALT_SPIM_MWCR_MWMOD
 * 
 * sequential transfer
 */
#define ALT_SPIM_MWCR_MWMOD_E_SEQ       0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_MWCR_MWMOD register field. */
#define ALT_SPIM_MWCR_MWMOD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_MWCR_MWMOD register field. */
#define ALT_SPIM_MWCR_MWMOD_MSB        0
/* The width in bits of the ALT_SPIM_MWCR_MWMOD register field. */
#define ALT_SPIM_MWCR_MWMOD_WIDTH      1
/* The mask used to set the ALT_SPIM_MWCR_MWMOD register field value. */
#define ALT_SPIM_MWCR_MWMOD_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIM_MWCR_MWMOD register field value. */
#define ALT_SPIM_MWCR_MWMOD_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIM_MWCR_MWMOD register field. */
#define ALT_SPIM_MWCR_MWMOD_RESET      0x0
/* Extracts the ALT_SPIM_MWCR_MWMOD field value from a register. */
#define ALT_SPIM_MWCR_MWMOD_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIM_MWCR_MWMOD register field value suitable for setting the register. */
#define ALT_SPIM_MWCR_MWMOD_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Microwire Control - mdd
 * 
 * Defines the direction of the data word when the Microwire serial protocol is
 * used.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description              
 * :--------------------------|:------|:--------------------------
 *  ALT_SPIM_MWCR_MDD_E_RXMOD | 0x0   | SPI Master receives data 
 *  ALT_SPIM_MWCR_MDD_E_TXMOD | 0x1   | SPI Master transmits data
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_MWCR_MDD
 * 
 * SPI Master receives data
 */
#define ALT_SPIM_MWCR_MDD_E_RXMOD   0x0
/*
 * Enumerated value for register field ALT_SPIM_MWCR_MDD
 * 
 * SPI Master transmits data
 */
#define ALT_SPIM_MWCR_MDD_E_TXMOD   0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_MWCR_MDD register field. */
#define ALT_SPIM_MWCR_MDD_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SPIM_MWCR_MDD register field. */
#define ALT_SPIM_MWCR_MDD_MSB        1
/* The width in bits of the ALT_SPIM_MWCR_MDD register field. */
#define ALT_SPIM_MWCR_MDD_WIDTH      1
/* The mask used to set the ALT_SPIM_MWCR_MDD register field value. */
#define ALT_SPIM_MWCR_MDD_SET_MSK    0x00000002
/* The mask used to clear the ALT_SPIM_MWCR_MDD register field value. */
#define ALT_SPIM_MWCR_MDD_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SPIM_MWCR_MDD register field. */
#define ALT_SPIM_MWCR_MDD_RESET      0x0
/* Extracts the ALT_SPIM_MWCR_MDD field value from a register. */
#define ALT_SPIM_MWCR_MDD_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SPIM_MWCR_MDD register field value suitable for setting the register. */
#define ALT_SPIM_MWCR_MDD_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Microwire Handshaking - mhs
 * 
 * Used to enable and disable the busy/ready handshaking interface for the
 * Microwire protocol. When enabled, the SPI Master checks for a ready status from
 * the target slave, after the transfer of the last data/control bit, before
 * clearing the BUSY status in the SR register.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                     | Value | Description                      
 * :-------------------------|:------|:----------------------------------
 *  ALT_SPIM_MWCR_MHS_E_DISD | 0x0   | Handshaking interface is disabled
 *  ALT_SPIM_MWCR_MHS_E_END  | 0x1   | Handshaking interface is enabled 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_MWCR_MHS
 * 
 * Handshaking interface is disabled
 */
#define ALT_SPIM_MWCR_MHS_E_DISD    0x0
/*
 * Enumerated value for register field ALT_SPIM_MWCR_MHS
 * 
 * Handshaking interface is enabled
 */
#define ALT_SPIM_MWCR_MHS_E_END     0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_MWCR_MHS register field. */
#define ALT_SPIM_MWCR_MHS_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SPIM_MWCR_MHS register field. */
#define ALT_SPIM_MWCR_MHS_MSB        2
/* The width in bits of the ALT_SPIM_MWCR_MHS register field. */
#define ALT_SPIM_MWCR_MHS_WIDTH      1
/* The mask used to set the ALT_SPIM_MWCR_MHS register field value. */
#define ALT_SPIM_MWCR_MHS_SET_MSK    0x00000004
/* The mask used to clear the ALT_SPIM_MWCR_MHS register field value. */
#define ALT_SPIM_MWCR_MHS_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SPIM_MWCR_MHS register field. */
#define ALT_SPIM_MWCR_MHS_RESET      0x0
/* Extracts the ALT_SPIM_MWCR_MHS field value from a register. */
#define ALT_SPIM_MWCR_MHS_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SPIM_MWCR_MHS register field value suitable for setting the register. */
#define ALT_SPIM_MWCR_MHS_SET(value) (((value) << 2) & 0x00000004)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_MWCR.
 */
struct ALT_SPIM_MWCR_s
{
    uint32_t  mwmod :  1;  /* Microwire Transfer Mode */
    uint32_t  mdd   :  1;  /* Microwire Control */
    uint32_t  mhs   :  1;  /* Microwire Handshaking */
    uint32_t        : 29;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_MWCR. */
typedef volatile struct ALT_SPIM_MWCR_s  ALT_SPIM_MWCR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_MWCR register from the beginning of the component. */
#define ALT_SPIM_MWCR_OFST        0xc
/* The address of the ALT_SPIM_MWCR register. */
#define ALT_SPIM_MWCR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_MWCR_OFST))

/*
 * Register : Slave Enable Register - ser
 * 
 * The register enables the individual slave select output lines from the SPI
 * Master. Up to 4 slave-select output pins are available on the SPI Master. You
 * cannot write to this register when SPI Master is busy and when SPI_EN = 1.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description             
 * :-------|:-------|:------|:-------------------------
 *  [3:0]  | RW     | 0x0   | Slave Select Enable Flag
 *  [31:4] | ???    | 0x0   | *UNDEFINED*             
 * 
 */
/*
 * Field : Slave Select Enable Flag - ser
 * 
 * Each bit in this register corresponds to a slave select line (spim_ss_x_n] from
 * the SPI Master. When a bit in this register is set (1), the corresponding slave
 * select line from the master is activated when a serial transfer begins. It
 * should be noted that setting or clearing bits in this register have no effect on
 * the corresponding slave select outputs until a transfer is started. Before
 * beginning a transfer, you should enable the bit in this register that
 * corresponds to the slave device with which the master wants to communicate. When
 * not operating in broadcast mode, only one bit in this field should be set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description         
 * :-------------------------------|:------|:---------------------
 *  ALT_SPIM_SER_SER_E_NOTSELECTED | 0x0   | Slave x Not Selected
 *  ALT_SPIM_SER_SER_E_SELECTED    | 0x1   | Slave x Selected    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_SER_SER
 * 
 * Slave x Not Selected
 */
#define ALT_SPIM_SER_SER_E_NOTSELECTED  0x0
/*
 * Enumerated value for register field ALT_SPIM_SER_SER
 * 
 * Slave x Selected
 */
#define ALT_SPIM_SER_SER_E_SELECTED     0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_SER_SER register field. */
#define ALT_SPIM_SER_SER_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_SER_SER register field. */
#define ALT_SPIM_SER_SER_MSB        3
/* The width in bits of the ALT_SPIM_SER_SER register field. */
#define ALT_SPIM_SER_SER_WIDTH      4
/* The mask used to set the ALT_SPIM_SER_SER register field value. */
#define ALT_SPIM_SER_SER_SET_MSK    0x0000000f
/* The mask used to clear the ALT_SPIM_SER_SER register field value. */
#define ALT_SPIM_SER_SER_CLR_MSK    0xfffffff0
/* The reset value of the ALT_SPIM_SER_SER register field. */
#define ALT_SPIM_SER_SER_RESET      0x0
/* Extracts the ALT_SPIM_SER_SER field value from a register. */
#define ALT_SPIM_SER_SER_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_SPIM_SER_SER register field value suitable for setting the register. */
#define ALT_SPIM_SER_SER_SET(value) (((value) << 0) & 0x0000000f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_SER.
 */
struct ALT_SPIM_SER_s
{
    uint32_t  ser :  4;  /* Slave Select Enable Flag */
    uint32_t      : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_SER. */
typedef volatile struct ALT_SPIM_SER_s  ALT_SPIM_SER_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_SER register from the beginning of the component. */
#define ALT_SPIM_SER_OFST        0x10
/* The address of the ALT_SPIM_SER register. */
#define ALT_SPIM_SER_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_SER_OFST))

/*
 * Register : Baud Rate Select Register - baudr
 * 
 * This register derives the frequency of the serial clock that regulates the data
 * transfer. The 16-bit field in this register defines the spi_m_clk divider value.
 * It is impossible to write to this register when the SPI Master is enabled. The
 * SPI Master is enabled and disabled by writing to the SPIENR register.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description      
 * :--------|:-------|:------|:------------------
 *  [15:0]  | RW     | 0x0   | SPI Clock Divider
 *  [31:16] | ???    | 0x0   | *UNDEFINED*      
 * 
 */
/*
 * Field : SPI Clock Divider - sckdv
 * 
 * The LSB for this field is always set to 0 and is unaffected by a write
 * operation, which ensures an even value is held in this register. If the value is
 * 0, the serial output clock (spim_sclk_out) is disabled. The frequency of the
 * spim_sclk_out  is derived from the following equation:
 * 
 * Fspim_sclk_out = Fspi_m_clk/SCKDV
 * 
 * where SCKDV is any even value between 2 and 65534. For example:
 * 
 * for Fspi_m_clk = 3.6864MHz and SCKDV =2
 * 
 * Fspim_sclk_out = 3.6864/2 = 1.8432MHz
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIM_BAUDR_SCKDV register field. */
#define ALT_SPIM_BAUDR_SCKDV_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_BAUDR_SCKDV register field. */
#define ALT_SPIM_BAUDR_SCKDV_MSB        15
/* The width in bits of the ALT_SPIM_BAUDR_SCKDV register field. */
#define ALT_SPIM_BAUDR_SCKDV_WIDTH      16
/* The mask used to set the ALT_SPIM_BAUDR_SCKDV register field value. */
#define ALT_SPIM_BAUDR_SCKDV_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_SPIM_BAUDR_SCKDV register field value. */
#define ALT_SPIM_BAUDR_SCKDV_CLR_MSK    0xffff0000
/* The reset value of the ALT_SPIM_BAUDR_SCKDV register field. */
#define ALT_SPIM_BAUDR_SCKDV_RESET      0x0
/* Extracts the ALT_SPIM_BAUDR_SCKDV field value from a register. */
#define ALT_SPIM_BAUDR_SCKDV_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_SPIM_BAUDR_SCKDV register field value suitable for setting the register. */
#define ALT_SPIM_BAUDR_SCKDV_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_BAUDR.
 */
struct ALT_SPIM_BAUDR_s
{
    uint32_t  sckdv : 16;  /* SPI Clock Divider */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_BAUDR. */
typedef volatile struct ALT_SPIM_BAUDR_s  ALT_SPIM_BAUDR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_BAUDR register from the beginning of the component. */
#define ALT_SPIM_BAUDR_OFST        0x14
/* The address of the ALT_SPIM_BAUDR register. */
#define ALT_SPIM_BAUDR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_BAUDR_OFST))

/*
 * Register : Transmit FIFO Threshold Level Register - txftlr
 * 
 * This register controls the threshold value for the transmit FIFO memory. It is
 * impossible to write to this register when the SPI Master is enabled. The SPI
 * Master is enabled and disabled by writing to the SPIENR register.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [7:0]  | RW     | 0x0   | Transmit FIFO Threshold Level
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : Transmit FIFO Threshold Level - tft
 * 
 * Controls the level of entries (or below) at which the transmit FIFO controller
 * triggers an interrupt. When the number of transmit FIFO entries is less than or
 * equal to this value, the transmit FIFO empty interrupt is triggered.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIM_TXFTLR_TFT register field. */
#define ALT_SPIM_TXFTLR_TFT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_TXFTLR_TFT register field. */
#define ALT_SPIM_TXFTLR_TFT_MSB        7
/* The width in bits of the ALT_SPIM_TXFTLR_TFT register field. */
#define ALT_SPIM_TXFTLR_TFT_WIDTH      8
/* The mask used to set the ALT_SPIM_TXFTLR_TFT register field value. */
#define ALT_SPIM_TXFTLR_TFT_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SPIM_TXFTLR_TFT register field value. */
#define ALT_SPIM_TXFTLR_TFT_CLR_MSK    0xffffff00
/* The reset value of the ALT_SPIM_TXFTLR_TFT register field. */
#define ALT_SPIM_TXFTLR_TFT_RESET      0x0
/* Extracts the ALT_SPIM_TXFTLR_TFT field value from a register. */
#define ALT_SPIM_TXFTLR_TFT_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SPIM_TXFTLR_TFT register field value suitable for setting the register. */
#define ALT_SPIM_TXFTLR_TFT_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_TXFTLR.
 */
struct ALT_SPIM_TXFTLR_s
{
    uint32_t  tft :  8;  /* Transmit FIFO Threshold Level */
    uint32_t      : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_TXFTLR. */
typedef volatile struct ALT_SPIM_TXFTLR_s  ALT_SPIM_TXFTLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_TXFTLR register from the beginning of the component. */
#define ALT_SPIM_TXFTLR_OFST        0x18
/* The address of the ALT_SPIM_TXFTLR register. */
#define ALT_SPIM_TXFTLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_TXFTLR_OFST))

/*
 * Register : Receive FIFO Threshold Level Register - rxftlr
 * 
 * This register controls the threshold value for the receive FIFO memory. It is
 * impossible to write to this register when the SPI Master is enabled. The SPI
 * Master is enabled and disabled by writing to the SPIENR register.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                 
 * :-------|:-------|:------|:-----------------------------
 *  [7:0]  | RW     | 0x0   | Receive FIFO Threshold Level
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                 
 * 
 */
/*
 * Field : Receive FIFO Threshold Level - rft
 * 
 * Controls the level of entries (or above) at which the receive FIFO controller
 * triggers an interrupt. When the number of receive FIFO entries is greater than
 * or equal to this value + 1, the receive FIFO full interrupt is triggered.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIM_RXFTLR_RFT register field. */
#define ALT_SPIM_RXFTLR_RFT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_RXFTLR_RFT register field. */
#define ALT_SPIM_RXFTLR_RFT_MSB        7
/* The width in bits of the ALT_SPIM_RXFTLR_RFT register field. */
#define ALT_SPIM_RXFTLR_RFT_WIDTH      8
/* The mask used to set the ALT_SPIM_RXFTLR_RFT register field value. */
#define ALT_SPIM_RXFTLR_RFT_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SPIM_RXFTLR_RFT register field value. */
#define ALT_SPIM_RXFTLR_RFT_CLR_MSK    0xffffff00
/* The reset value of the ALT_SPIM_RXFTLR_RFT register field. */
#define ALT_SPIM_RXFTLR_RFT_RESET      0x0
/* Extracts the ALT_SPIM_RXFTLR_RFT field value from a register. */
#define ALT_SPIM_RXFTLR_RFT_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SPIM_RXFTLR_RFT register field value suitable for setting the register. */
#define ALT_SPIM_RXFTLR_RFT_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_RXFTLR.
 */
struct ALT_SPIM_RXFTLR_s
{
    uint32_t  rft :  8;  /* Receive FIFO Threshold Level */
    uint32_t      : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_RXFTLR. */
typedef volatile struct ALT_SPIM_RXFTLR_s  ALT_SPIM_RXFTLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_RXFTLR register from the beginning of the component. */
#define ALT_SPIM_RXFTLR_OFST        0x1c
/* The address of the ALT_SPIM_RXFTLR register. */
#define ALT_SPIM_RXFTLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_RXFTLR_OFST))

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
/* The Least Significant Bit (LSB) position of the ALT_SPIM_TXFLR_TXTFL register field. */
#define ALT_SPIM_TXFLR_TXTFL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_TXFLR_TXTFL register field. */
#define ALT_SPIM_TXFLR_TXTFL_MSB        8
/* The width in bits of the ALT_SPIM_TXFLR_TXTFL register field. */
#define ALT_SPIM_TXFLR_TXTFL_WIDTH      9
/* The mask used to set the ALT_SPIM_TXFLR_TXTFL register field value. */
#define ALT_SPIM_TXFLR_TXTFL_SET_MSK    0x000001ff
/* The mask used to clear the ALT_SPIM_TXFLR_TXTFL register field value. */
#define ALT_SPIM_TXFLR_TXTFL_CLR_MSK    0xfffffe00
/* The reset value of the ALT_SPIM_TXFLR_TXTFL register field. */
#define ALT_SPIM_TXFLR_TXTFL_RESET      0x0
/* Extracts the ALT_SPIM_TXFLR_TXTFL field value from a register. */
#define ALT_SPIM_TXFLR_TXTFL_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_SPIM_TXFLR_TXTFL register field value suitable for setting the register. */
#define ALT_SPIM_TXFLR_TXTFL_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_TXFLR.
 */
struct ALT_SPIM_TXFLR_s
{
    const uint32_t  txtfl :  9;  /* Transmit FIFO Level */
    uint32_t              : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_TXFLR. */
typedef volatile struct ALT_SPIM_TXFLR_s  ALT_SPIM_TXFLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_TXFLR register from the beginning of the component. */
#define ALT_SPIM_TXFLR_OFST        0x20
/* The address of the ALT_SPIM_TXFLR register. */
#define ALT_SPIM_TXFLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_TXFLR_OFST))

/*
 * Register : Receive FIFO Level Register - rxflr
 * 
 * This register contains the number of valid data entries in the receive FIFO
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
/* The Least Significant Bit (LSB) position of the ALT_SPIM_RXFLR_RXTFL register field. */
#define ALT_SPIM_RXFLR_RXTFL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_RXFLR_RXTFL register field. */
#define ALT_SPIM_RXFLR_RXTFL_MSB        8
/* The width in bits of the ALT_SPIM_RXFLR_RXTFL register field. */
#define ALT_SPIM_RXFLR_RXTFL_WIDTH      9
/* The mask used to set the ALT_SPIM_RXFLR_RXTFL register field value. */
#define ALT_SPIM_RXFLR_RXTFL_SET_MSK    0x000001ff
/* The mask used to clear the ALT_SPIM_RXFLR_RXTFL register field value. */
#define ALT_SPIM_RXFLR_RXTFL_CLR_MSK    0xfffffe00
/* The reset value of the ALT_SPIM_RXFLR_RXTFL register field. */
#define ALT_SPIM_RXFLR_RXTFL_RESET      0x0
/* Extracts the ALT_SPIM_RXFLR_RXTFL field value from a register. */
#define ALT_SPIM_RXFLR_RXTFL_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_SPIM_RXFLR_RXTFL register field value suitable for setting the register. */
#define ALT_SPIM_RXFLR_RXTFL_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_RXFLR.
 */
struct ALT_SPIM_RXFLR_s
{
    const uint32_t  rxtfl :  9;  /* Receive FIFO Level */
    uint32_t              : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_RXFLR. */
typedef volatile struct ALT_SPIM_RXFLR_s  ALT_SPIM_RXFLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_RXFLR register from the beginning of the component. */
#define ALT_SPIM_RXFLR_OFST        0x24
/* The address of the ALT_SPIM_RXFLR register. */
#define ALT_SPIM_RXFLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_RXFLR_OFST))

/*
 * Register : Status Register - sr
 * 
 * This register is used to indicate the current transfer status, FIFO status, and
 * any transmission/reception errors that may have occurred. The status register
 * may be read at any time. None of the bits in this register request an interrupt.
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
 *  [31:5] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : SPI Busy Flag - busy
 * 
 * Reports the staus of a serial transfer
 * 
 * Field Enumeration Values:
 * 
 *  Enum                     | Value | Description                              
 * :-------------------------|:------|:------------------------------------------
 *  ALT_SPIM_SR_BUSY_E_INACT | 0x0   | SPI Master is inactive (idle or disabled)
 *  ALT_SPIM_SR_BUSY_E_ACT   | 0x1   | SPI Master is actively transferring data 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_SR_BUSY
 * 
 * SPI Master is inactive (idle or disabled)
 */
#define ALT_SPIM_SR_BUSY_E_INACT    0x0
/*
 * Enumerated value for register field ALT_SPIM_SR_BUSY
 * 
 * SPI Master is actively transferring data
 */
#define ALT_SPIM_SR_BUSY_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_SR_BUSY register field. */
#define ALT_SPIM_SR_BUSY_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_SR_BUSY register field. */
#define ALT_SPIM_SR_BUSY_MSB        0
/* The width in bits of the ALT_SPIM_SR_BUSY register field. */
#define ALT_SPIM_SR_BUSY_WIDTH      1
/* The mask used to set the ALT_SPIM_SR_BUSY register field value. */
#define ALT_SPIM_SR_BUSY_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIM_SR_BUSY register field value. */
#define ALT_SPIM_SR_BUSY_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIM_SR_BUSY register field. */
#define ALT_SPIM_SR_BUSY_RESET      0x0
/* Extracts the ALT_SPIM_SR_BUSY field value from a register. */
#define ALT_SPIM_SR_BUSY_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIM_SR_BUSY register field value suitable for setting the register. */
#define ALT_SPIM_SR_BUSY_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Transmit FIFO Not Full - tfnf
 * 
 * Reports transmit FIFO condition.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description              
 * :---------------------------|:------|:--------------------------
 *  ALT_SPIM_SR_TFNF_E_FULL    | 0x0   | Transmit FIFO is full    
 *  ALT_SPIM_SR_TFNF_E_NOTFULL | 0x1   | Transmit FIFO is not full
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_SR_TFNF
 * 
 * Transmit FIFO is full
 */
#define ALT_SPIM_SR_TFNF_E_FULL     0x0
/*
 * Enumerated value for register field ALT_SPIM_SR_TFNF
 * 
 * Transmit FIFO is not full
 */
#define ALT_SPIM_SR_TFNF_E_NOTFULL  0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_SR_TFNF register field. */
#define ALT_SPIM_SR_TFNF_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SPIM_SR_TFNF register field. */
#define ALT_SPIM_SR_TFNF_MSB        1
/* The width in bits of the ALT_SPIM_SR_TFNF register field. */
#define ALT_SPIM_SR_TFNF_WIDTH      1
/* The mask used to set the ALT_SPIM_SR_TFNF register field value. */
#define ALT_SPIM_SR_TFNF_SET_MSK    0x00000002
/* The mask used to clear the ALT_SPIM_SR_TFNF register field value. */
#define ALT_SPIM_SR_TFNF_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SPIM_SR_TFNF register field. */
#define ALT_SPIM_SR_TFNF_RESET      0x1
/* Extracts the ALT_SPIM_SR_TFNF field value from a register. */
#define ALT_SPIM_SR_TFNF_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SPIM_SR_TFNF register field value suitable for setting the register. */
#define ALT_SPIM_SR_TFNF_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Transmit FIFO Empty - tfe
 * 
 * Reports transmit FIFO condition.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description               
 * :---------------------------|:------|:---------------------------
 *  ALT_SPIM_SR_TFE_E_EMPTY    | 0x1   | Transmit FIFO is empty    
 *  ALT_SPIM_SR_TFE_E_NOTEMPTY | 0x0   | Transmit FIFO is not empty
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_SR_TFE
 * 
 * Transmit FIFO is empty
 */
#define ALT_SPIM_SR_TFE_E_EMPTY     0x1
/*
 * Enumerated value for register field ALT_SPIM_SR_TFE
 * 
 * Transmit FIFO is not empty
 */
#define ALT_SPIM_SR_TFE_E_NOTEMPTY  0x0

/* The Least Significant Bit (LSB) position of the ALT_SPIM_SR_TFE register field. */
#define ALT_SPIM_SR_TFE_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SPIM_SR_TFE register field. */
#define ALT_SPIM_SR_TFE_MSB        2
/* The width in bits of the ALT_SPIM_SR_TFE register field. */
#define ALT_SPIM_SR_TFE_WIDTH      1
/* The mask used to set the ALT_SPIM_SR_TFE register field value. */
#define ALT_SPIM_SR_TFE_SET_MSK    0x00000004
/* The mask used to clear the ALT_SPIM_SR_TFE register field value. */
#define ALT_SPIM_SR_TFE_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SPIM_SR_TFE register field. */
#define ALT_SPIM_SR_TFE_RESET      0x1
/* Extracts the ALT_SPIM_SR_TFE field value from a register. */
#define ALT_SPIM_SR_TFE_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SPIM_SR_TFE register field value suitable for setting the register. */
#define ALT_SPIM_SR_TFE_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Receive FIFO Not Empty - rfne
 * 
 * Reports receive FIFO condition.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description              
 * :----------------------------|:------|:--------------------------
 *  ALT_SPIM_SR_RFNE_E_EMPTY    | 0x0   | Receive FIFO is empty    
 *  ALT_SPIM_SR_RFNE_E_NOTEMPTY | 0x1   | Receive FIFO is not empty
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_SR_RFNE
 * 
 * Receive FIFO is empty
 */
#define ALT_SPIM_SR_RFNE_E_EMPTY    0x0
/*
 * Enumerated value for register field ALT_SPIM_SR_RFNE
 * 
 * Receive FIFO is not empty
 */
#define ALT_SPIM_SR_RFNE_E_NOTEMPTY 0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_SR_RFNE register field. */
#define ALT_SPIM_SR_RFNE_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SPIM_SR_RFNE register field. */
#define ALT_SPIM_SR_RFNE_MSB        3
/* The width in bits of the ALT_SPIM_SR_RFNE register field. */
#define ALT_SPIM_SR_RFNE_WIDTH      1
/* The mask used to set the ALT_SPIM_SR_RFNE register field value. */
#define ALT_SPIM_SR_RFNE_SET_MSK    0x00000008
/* The mask used to clear the ALT_SPIM_SR_RFNE register field value. */
#define ALT_SPIM_SR_RFNE_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SPIM_SR_RFNE register field. */
#define ALT_SPIM_SR_RFNE_RESET      0x0
/* Extracts the ALT_SPIM_SR_RFNE field value from a register. */
#define ALT_SPIM_SR_RFNE_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SPIM_SR_RFNE register field value suitable for setting the register. */
#define ALT_SPIM_SR_RFNE_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Receive FIFO Full - rff
 * 
 * Reports receive FIFO condition.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description             
 * :--------------------------|:------|:-------------------------
 *  ALT_SPIM_SR_RFF_E_NOTFULL | 0x0   | Receive FIFO is not full
 *  ALT_SPIM_SR_RFF_E_FULL    | 0x1   | Receive FIFO is full    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_SR_RFF
 * 
 * Receive FIFO is not full
 */
#define ALT_SPIM_SR_RFF_E_NOTFULL   0x0
/*
 * Enumerated value for register field ALT_SPIM_SR_RFF
 * 
 * Receive FIFO is full
 */
#define ALT_SPIM_SR_RFF_E_FULL      0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_SR_RFF register field. */
#define ALT_SPIM_SR_RFF_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SPIM_SR_RFF register field. */
#define ALT_SPIM_SR_RFF_MSB        4
/* The width in bits of the ALT_SPIM_SR_RFF register field. */
#define ALT_SPIM_SR_RFF_WIDTH      1
/* The mask used to set the ALT_SPIM_SR_RFF register field value. */
#define ALT_SPIM_SR_RFF_SET_MSK    0x00000010
/* The mask used to clear the ALT_SPIM_SR_RFF register field value. */
#define ALT_SPIM_SR_RFF_CLR_MSK    0xffffffef
/* The reset value of the ALT_SPIM_SR_RFF register field. */
#define ALT_SPIM_SR_RFF_RESET      0x0
/* Extracts the ALT_SPIM_SR_RFF field value from a register. */
#define ALT_SPIM_SR_RFF_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SPIM_SR_RFF register field value suitable for setting the register. */
#define ALT_SPIM_SR_RFF_SET(value) (((value) << 4) & 0x00000010)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_SR.
 */
struct ALT_SPIM_SR_s
{
    const uint32_t  busy :  1;  /* SPI Busy Flag */
    const uint32_t  tfnf :  1;  /* Transmit FIFO Not Full */
    const uint32_t  tfe  :  1;  /* Transmit FIFO Empty */
    const uint32_t  rfne :  1;  /* Receive FIFO Not Empty */
    const uint32_t  rff  :  1;  /* Receive FIFO Full */
    uint32_t             : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_SR. */
typedef volatile struct ALT_SPIM_SR_s  ALT_SPIM_SR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_SR register from the beginning of the component. */
#define ALT_SPIM_SR_OFST        0x28
/* The address of the ALT_SPIM_SR register. */
#define ALT_SPIM_SR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_SR_OFST))

/*
 * Register : Interrupt Mask Register - imr
 * 
 * This register masks or enables all interrupts generated by the SPI Master.
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
 *  [31:5] | ???    | 0x1   | *UNDEFINED*                          
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
 *  ALT_SPIM_IMR_TXEIM_E_MSKED | 0x0   | spi_txe_intr interrupt is masked (disabled)
 *  ALT_SPIM_IMR_TXEIM_E_END   | 0x1   | spi_txe_intr interrupt is enabled          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_IMR_TXEIM
 * 
 * spi_txe_intr interrupt is masked (disabled)
 */
#define ALT_SPIM_IMR_TXEIM_E_MSKED  0x0
/*
 * Enumerated value for register field ALT_SPIM_IMR_TXEIM
 * 
 * spi_txe_intr interrupt is enabled
 */
#define ALT_SPIM_IMR_TXEIM_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_IMR_TXEIM register field. */
#define ALT_SPIM_IMR_TXEIM_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_IMR_TXEIM register field. */
#define ALT_SPIM_IMR_TXEIM_MSB        0
/* The width in bits of the ALT_SPIM_IMR_TXEIM register field. */
#define ALT_SPIM_IMR_TXEIM_WIDTH      1
/* The mask used to set the ALT_SPIM_IMR_TXEIM register field value. */
#define ALT_SPIM_IMR_TXEIM_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIM_IMR_TXEIM register field value. */
#define ALT_SPIM_IMR_TXEIM_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIM_IMR_TXEIM register field. */
#define ALT_SPIM_IMR_TXEIM_RESET      0x1
/* Extracts the ALT_SPIM_IMR_TXEIM field value from a register. */
#define ALT_SPIM_IMR_TXEIM_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIM_IMR_TXEIM register field value suitable for setting the register. */
#define ALT_SPIM_IMR_TXEIM_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Transmit FIFO Overflow Interrupt Mask - txoim
 * 
 * Overflow Mask
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                
 * :---------------------------|:------|:--------------------------------------------
 *  ALT_SPIM_IMR_TXOIM_E_MSKED | 0x0   | spi_txo_intr interrupt is masked (disabled)
 *  ALT_SPIM_IMR_TXOIM_E_END   | 0x1   | spi_txo_intr interrupt is enabled          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_IMR_TXOIM
 * 
 * spi_txo_intr interrupt is masked (disabled)
 */
#define ALT_SPIM_IMR_TXOIM_E_MSKED  0x0
/*
 * Enumerated value for register field ALT_SPIM_IMR_TXOIM
 * 
 * spi_txo_intr interrupt is enabled
 */
#define ALT_SPIM_IMR_TXOIM_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_IMR_TXOIM register field. */
#define ALT_SPIM_IMR_TXOIM_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SPIM_IMR_TXOIM register field. */
#define ALT_SPIM_IMR_TXOIM_MSB        1
/* The width in bits of the ALT_SPIM_IMR_TXOIM register field. */
#define ALT_SPIM_IMR_TXOIM_WIDTH      1
/* The mask used to set the ALT_SPIM_IMR_TXOIM register field value. */
#define ALT_SPIM_IMR_TXOIM_SET_MSK    0x00000002
/* The mask used to clear the ALT_SPIM_IMR_TXOIM register field value. */
#define ALT_SPIM_IMR_TXOIM_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SPIM_IMR_TXOIM register field. */
#define ALT_SPIM_IMR_TXOIM_RESET      0x1
/* Extracts the ALT_SPIM_IMR_TXOIM field value from a register. */
#define ALT_SPIM_IMR_TXOIM_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SPIM_IMR_TXOIM register field value suitable for setting the register. */
#define ALT_SPIM_IMR_TXOIM_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Receive FIFO Underflow Interrupt Mask - rxuim
 * 
 * Underflow Mask
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                
 * :---------------------------|:------|:--------------------------------------------
 *  ALT_SPIM_IMR_RXUIM_E_MSKED | 0x0   | spi_rxu_intr interrupt is masked (disabled)
 *  ALT_SPIM_IMR_RXUIM_E_END   | 0x1   | spi_rxu_intr interrupt is enabled          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_IMR_RXUIM
 * 
 * spi_rxu_intr interrupt is masked (disabled)
 */
#define ALT_SPIM_IMR_RXUIM_E_MSKED  0x0
/*
 * Enumerated value for register field ALT_SPIM_IMR_RXUIM
 * 
 * spi_rxu_intr interrupt is enabled
 */
#define ALT_SPIM_IMR_RXUIM_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_IMR_RXUIM register field. */
#define ALT_SPIM_IMR_RXUIM_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SPIM_IMR_RXUIM register field. */
#define ALT_SPIM_IMR_RXUIM_MSB        2
/* The width in bits of the ALT_SPIM_IMR_RXUIM register field. */
#define ALT_SPIM_IMR_RXUIM_WIDTH      1
/* The mask used to set the ALT_SPIM_IMR_RXUIM register field value. */
#define ALT_SPIM_IMR_RXUIM_SET_MSK    0x00000004
/* The mask used to clear the ALT_SPIM_IMR_RXUIM register field value. */
#define ALT_SPIM_IMR_RXUIM_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SPIM_IMR_RXUIM register field. */
#define ALT_SPIM_IMR_RXUIM_RESET      0x1
/* Extracts the ALT_SPIM_IMR_RXUIM field value from a register. */
#define ALT_SPIM_IMR_RXUIM_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SPIM_IMR_RXUIM register field value suitable for setting the register. */
#define ALT_SPIM_IMR_RXUIM_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Receive FIFO Overflow Interrupt Mask - rxoim
 * 
 * Overflow Mask.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                
 * :---------------------------|:------|:--------------------------------------------
 *  ALT_SPIM_IMR_RXOIM_E_MSKED | 0x0   | spi_rxo_intr interrupt is masked (disabled)
 *  ALT_SPIM_IMR_RXOIM_E_END   | 0x1   | spi_rxo_intr interrupt is enabled          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_IMR_RXOIM
 * 
 * spi_rxo_intr interrupt is masked (disabled)
 */
#define ALT_SPIM_IMR_RXOIM_E_MSKED  0x0
/*
 * Enumerated value for register field ALT_SPIM_IMR_RXOIM
 * 
 * spi_rxo_intr interrupt is enabled
 */
#define ALT_SPIM_IMR_RXOIM_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_IMR_RXOIM register field. */
#define ALT_SPIM_IMR_RXOIM_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SPIM_IMR_RXOIM register field. */
#define ALT_SPIM_IMR_RXOIM_MSB        3
/* The width in bits of the ALT_SPIM_IMR_RXOIM register field. */
#define ALT_SPIM_IMR_RXOIM_WIDTH      1
/* The mask used to set the ALT_SPIM_IMR_RXOIM register field value. */
#define ALT_SPIM_IMR_RXOIM_SET_MSK    0x00000008
/* The mask used to clear the ALT_SPIM_IMR_RXOIM register field value. */
#define ALT_SPIM_IMR_RXOIM_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SPIM_IMR_RXOIM register field. */
#define ALT_SPIM_IMR_RXOIM_RESET      0x1
/* Extracts the ALT_SPIM_IMR_RXOIM field value from a register. */
#define ALT_SPIM_IMR_RXOIM_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SPIM_IMR_RXOIM register field value suitable for setting the register. */
#define ALT_SPIM_IMR_RXOIM_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Receive FIFO Full Interrupt Mask - rxfim
 * 
 * Full Mask
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                
 * :---------------------------|:------|:--------------------------------------------
 *  ALT_SPIM_IMR_RXFIM_E_MSKED | 0x0   | spi_rxf_intr interrupt is masked (disabled)
 *  ALT_SPIM_IMR_RXFIM_E_END   | 0x1   | spi_rxf_intr interrupt is enabled          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_IMR_RXFIM
 * 
 * spi_rxf_intr interrupt is masked (disabled)
 */
#define ALT_SPIM_IMR_RXFIM_E_MSKED  0x0
/*
 * Enumerated value for register field ALT_SPIM_IMR_RXFIM
 * 
 * spi_rxf_intr interrupt is enabled
 */
#define ALT_SPIM_IMR_RXFIM_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_IMR_RXFIM register field. */
#define ALT_SPIM_IMR_RXFIM_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SPIM_IMR_RXFIM register field. */
#define ALT_SPIM_IMR_RXFIM_MSB        4
/* The width in bits of the ALT_SPIM_IMR_RXFIM register field. */
#define ALT_SPIM_IMR_RXFIM_WIDTH      1
/* The mask used to set the ALT_SPIM_IMR_RXFIM register field value. */
#define ALT_SPIM_IMR_RXFIM_SET_MSK    0x00000010
/* The mask used to clear the ALT_SPIM_IMR_RXFIM register field value. */
#define ALT_SPIM_IMR_RXFIM_CLR_MSK    0xffffffef
/* The reset value of the ALT_SPIM_IMR_RXFIM register field. */
#define ALT_SPIM_IMR_RXFIM_RESET      0x1
/* Extracts the ALT_SPIM_IMR_RXFIM field value from a register. */
#define ALT_SPIM_IMR_RXFIM_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SPIM_IMR_RXFIM register field value suitable for setting the register. */
#define ALT_SPIM_IMR_RXFIM_SET(value) (((value) << 4) & 0x00000010)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_IMR.
 */
struct ALT_SPIM_IMR_s
{
    uint32_t  txeim :  1;  /* Transmit FIFO Empty Interrupt Mask */
    uint32_t  txoim :  1;  /* Transmit FIFO Overflow Interrupt Mask */
    uint32_t  rxuim :  1;  /* Receive FIFO Underflow Interrupt Mask */
    uint32_t  rxoim :  1;  /* Receive FIFO Overflow Interrupt Mask */
    uint32_t  rxfim :  1;  /* Receive FIFO Full Interrupt Mask */
    uint32_t        : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_IMR. */
typedef volatile struct ALT_SPIM_IMR_s  ALT_SPIM_IMR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_IMR register from the beginning of the component. */
#define ALT_SPIM_IMR_OFST        0x2c
/* The address of the ALT_SPIM_IMR register. */
#define ALT_SPIM_IMR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_IMR_OFST))

/*
 * Register : Interrupt Status Register - isr
 * 
 * This register reports the status of the SPI Master interrupts after they have
 * been masked.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                             
 * :-------|:-------|:------|:-----------------------------------------
 *  [0]    | R      | 0x0   | Transmit FIFO Empty Interrupt Status    
 *  [1]    | R      | 0x0   | Transmit FIFO Overflow Interrupt Status 
 *  [2]    | R      | 0x0   | Receive FIFO Underflow Interrupt Status 
 *  [3]    | R      | 0x0   | Receive FIFO Overflow Interrupt Status  
 *  [4]    | R      | 0x0   | Receive FIFO Full Interrupt Status      
 *  [5]    | R      | 0x0   | Multi-Master Contention Interrupt Status
 *  [31:6] | ???    | 0x0   | *UNDEFINED*                             
 * 
 */
/*
 * Field : Transmit FIFO Empty Interrupt Status - txeis
 * 
 * Empty status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                   
 * :---------------------------|:------|:-----------------------------------------------
 *  ALT_SPIM_ISR_TXEIS_E_INACT | 0x0   | spi_txe_intr interrupt is not active after    
 * :                           |       | masking                                       
 *  ALT_SPIM_ISR_TXEIS_E_ACT   | 0x1   | spi_txe_intr interrupt is active after masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_ISR_TXEIS
 * 
 * spi_txe_intr interrupt is not active after masking
 */
#define ALT_SPIM_ISR_TXEIS_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SPIM_ISR_TXEIS
 * 
 * spi_txe_intr interrupt is active after masking
 */
#define ALT_SPIM_ISR_TXEIS_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_ISR_TXEIS register field. */
#define ALT_SPIM_ISR_TXEIS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_ISR_TXEIS register field. */
#define ALT_SPIM_ISR_TXEIS_MSB        0
/* The width in bits of the ALT_SPIM_ISR_TXEIS register field. */
#define ALT_SPIM_ISR_TXEIS_WIDTH      1
/* The mask used to set the ALT_SPIM_ISR_TXEIS register field value. */
#define ALT_SPIM_ISR_TXEIS_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIM_ISR_TXEIS register field value. */
#define ALT_SPIM_ISR_TXEIS_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIM_ISR_TXEIS register field. */
#define ALT_SPIM_ISR_TXEIS_RESET      0x0
/* Extracts the ALT_SPIM_ISR_TXEIS field value from a register. */
#define ALT_SPIM_ISR_TXEIS_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIM_ISR_TXEIS register field value suitable for setting the register. */
#define ALT_SPIM_ISR_TXEIS_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Transmit FIFO Overflow Interrupt Status - txois
 * 
 * Overflow Status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                   
 * :---------------------------|:------|:-----------------------------------------------
 *  ALT_SPIM_ISR_TXOIS_E_INACT | 0x0   | spi_txo_intr interrupt is not active after    
 * :                           |       | masking                                       
 *  ALT_SPIM_ISR_TXOIS_E_ACT   | 0x1   | spi_txo_intr interrupt is active after masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_ISR_TXOIS
 * 
 * spi_txo_intr interrupt is not active after masking
 */
#define ALT_SPIM_ISR_TXOIS_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SPIM_ISR_TXOIS
 * 
 * spi_txo_intr interrupt is active after masking
 */
#define ALT_SPIM_ISR_TXOIS_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_ISR_TXOIS register field. */
#define ALT_SPIM_ISR_TXOIS_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SPIM_ISR_TXOIS register field. */
#define ALT_SPIM_ISR_TXOIS_MSB        1
/* The width in bits of the ALT_SPIM_ISR_TXOIS register field. */
#define ALT_SPIM_ISR_TXOIS_WIDTH      1
/* The mask used to set the ALT_SPIM_ISR_TXOIS register field value. */
#define ALT_SPIM_ISR_TXOIS_SET_MSK    0x00000002
/* The mask used to clear the ALT_SPIM_ISR_TXOIS register field value. */
#define ALT_SPIM_ISR_TXOIS_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SPIM_ISR_TXOIS register field. */
#define ALT_SPIM_ISR_TXOIS_RESET      0x0
/* Extracts the ALT_SPIM_ISR_TXOIS field value from a register. */
#define ALT_SPIM_ISR_TXOIS_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SPIM_ISR_TXOIS register field value suitable for setting the register. */
#define ALT_SPIM_ISR_TXOIS_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Receive FIFO Underflow Interrupt Status - rxuis
 * 
 * Underflow Status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                   
 * :---------------------------|:------|:-----------------------------------------------
 *  ALT_SPIM_ISR_RXUIS_E_INACT | 0x0   | spi_rxu_intr interrupt is not active after    
 * :                           |       | masking                                       
 *  ALT_SPIM_ISR_RXUIS_E_ACT   | 0x1   | spi_rxu_intr interrupt is active after masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_ISR_RXUIS
 * 
 * spi_rxu_intr interrupt is not active after masking
 */
#define ALT_SPIM_ISR_RXUIS_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SPIM_ISR_RXUIS
 * 
 * spi_rxu_intr interrupt is active after masking
 */
#define ALT_SPIM_ISR_RXUIS_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_ISR_RXUIS register field. */
#define ALT_SPIM_ISR_RXUIS_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SPIM_ISR_RXUIS register field. */
#define ALT_SPIM_ISR_RXUIS_MSB        2
/* The width in bits of the ALT_SPIM_ISR_RXUIS register field. */
#define ALT_SPIM_ISR_RXUIS_WIDTH      1
/* The mask used to set the ALT_SPIM_ISR_RXUIS register field value. */
#define ALT_SPIM_ISR_RXUIS_SET_MSK    0x00000004
/* The mask used to clear the ALT_SPIM_ISR_RXUIS register field value. */
#define ALT_SPIM_ISR_RXUIS_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SPIM_ISR_RXUIS register field. */
#define ALT_SPIM_ISR_RXUIS_RESET      0x0
/* Extracts the ALT_SPIM_ISR_RXUIS field value from a register. */
#define ALT_SPIM_ISR_RXUIS_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SPIM_ISR_RXUIS register field value suitable for setting the register. */
#define ALT_SPIM_ISR_RXUIS_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Receive FIFO Overflow Interrupt Status - rxois
 * 
 * Overflow Status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                   
 * :---------------------------|:------|:-----------------------------------------------
 *  ALT_SPIM_ISR_RXOIS_E_INACT | 0x0   | spi_rxo_intr interrupt is not active after    
 * :                           |       | masking                                       
 *  ALT_SPIM_ISR_RXOIS_E_ACT   | 0x1   | spi_rxo_intr interrupt is active after masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_ISR_RXOIS
 * 
 * spi_rxo_intr interrupt is not active after masking
 */
#define ALT_SPIM_ISR_RXOIS_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SPIM_ISR_RXOIS
 * 
 * spi_rxo_intr interrupt is active after masking
 */
#define ALT_SPIM_ISR_RXOIS_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_ISR_RXOIS register field. */
#define ALT_SPIM_ISR_RXOIS_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SPIM_ISR_RXOIS register field. */
#define ALT_SPIM_ISR_RXOIS_MSB        3
/* The width in bits of the ALT_SPIM_ISR_RXOIS register field. */
#define ALT_SPIM_ISR_RXOIS_WIDTH      1
/* The mask used to set the ALT_SPIM_ISR_RXOIS register field value. */
#define ALT_SPIM_ISR_RXOIS_SET_MSK    0x00000008
/* The mask used to clear the ALT_SPIM_ISR_RXOIS register field value. */
#define ALT_SPIM_ISR_RXOIS_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SPIM_ISR_RXOIS register field. */
#define ALT_SPIM_ISR_RXOIS_RESET      0x0
/* Extracts the ALT_SPIM_ISR_RXOIS field value from a register. */
#define ALT_SPIM_ISR_RXOIS_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SPIM_ISR_RXOIS register field value suitable for setting the register. */
#define ALT_SPIM_ISR_RXOIS_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Receive FIFO Full Interrupt Status - rxfis
 * 
 * Full Status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                 
 * :---------------------------|:------|:---------------------------------------------
 *  ALT_SPIM_ISR_RXFIS_E_INACT | 0x0   | spi_rxf_intr interrupt is not active after  
 * :                           |       | masking                                     
 *  ALT_SPIM_ISR_RXFIS_E_ACT   | 0x1   | spi_rxf_intr interrupt is full after masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_ISR_RXFIS
 * 
 * spi_rxf_intr interrupt is not active after masking
 */
#define ALT_SPIM_ISR_RXFIS_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SPIM_ISR_RXFIS
 * 
 * spi_rxf_intr interrupt is full after masking
 */
#define ALT_SPIM_ISR_RXFIS_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_ISR_RXFIS register field. */
#define ALT_SPIM_ISR_RXFIS_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SPIM_ISR_RXFIS register field. */
#define ALT_SPIM_ISR_RXFIS_MSB        4
/* The width in bits of the ALT_SPIM_ISR_RXFIS register field. */
#define ALT_SPIM_ISR_RXFIS_WIDTH      1
/* The mask used to set the ALT_SPIM_ISR_RXFIS register field value. */
#define ALT_SPIM_ISR_RXFIS_SET_MSK    0x00000010
/* The mask used to clear the ALT_SPIM_ISR_RXFIS register field value. */
#define ALT_SPIM_ISR_RXFIS_CLR_MSK    0xffffffef
/* The reset value of the ALT_SPIM_ISR_RXFIS register field. */
#define ALT_SPIM_ISR_RXFIS_RESET      0x0
/* Extracts the ALT_SPIM_ISR_RXFIS field value from a register. */
#define ALT_SPIM_ISR_RXFIS_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SPIM_ISR_RXFIS register field value suitable for setting the register. */
#define ALT_SPIM_ISR_RXFIS_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Multi-Master Contention Interrupt Status - mstis
 * 
 * Multi-master contention status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                
 * :---------------------------|:------|:--------------------------------------------
 *  ALT_SPIM_ISR_MSTIS_E_INACT | 0x0   | 0 = ssi_mst_intr interrupt not active after
 * :                           |       | masking                                    
 *  ALT_SPIM_ISR_MSTIS_E_ACT   | 0x1   | 1 = ssi_mst_intr interrupt is active after 
 * :                           |       | masking                                    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_ISR_MSTIS
 * 
 * 0 = ssi_mst_intr interrupt not active after masking
 */
#define ALT_SPIM_ISR_MSTIS_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SPIM_ISR_MSTIS
 * 
 * 1 = ssi_mst_intr interrupt is active after masking
 */
#define ALT_SPIM_ISR_MSTIS_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_ISR_MSTIS register field. */
#define ALT_SPIM_ISR_MSTIS_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_SPIM_ISR_MSTIS register field. */
#define ALT_SPIM_ISR_MSTIS_MSB        5
/* The width in bits of the ALT_SPIM_ISR_MSTIS register field. */
#define ALT_SPIM_ISR_MSTIS_WIDTH      1
/* The mask used to set the ALT_SPIM_ISR_MSTIS register field value. */
#define ALT_SPIM_ISR_MSTIS_SET_MSK    0x00000020
/* The mask used to clear the ALT_SPIM_ISR_MSTIS register field value. */
#define ALT_SPIM_ISR_MSTIS_CLR_MSK    0xffffffdf
/* The reset value of the ALT_SPIM_ISR_MSTIS register field. */
#define ALT_SPIM_ISR_MSTIS_RESET      0x0
/* Extracts the ALT_SPIM_ISR_MSTIS field value from a register. */
#define ALT_SPIM_ISR_MSTIS_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_SPIM_ISR_MSTIS register field value suitable for setting the register. */
#define ALT_SPIM_ISR_MSTIS_SET(value) (((value) << 5) & 0x00000020)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_ISR.
 */
struct ALT_SPIM_ISR_s
{
    const uint32_t  txeis :  1;  /* Transmit FIFO Empty Interrupt Status */
    const uint32_t  txois :  1;  /* Transmit FIFO Overflow Interrupt Status */
    const uint32_t  rxuis :  1;  /* Receive FIFO Underflow Interrupt Status */
    const uint32_t  rxois :  1;  /* Receive FIFO Overflow Interrupt Status */
    const uint32_t  rxfis :  1;  /* Receive FIFO Full Interrupt Status */
    const uint32_t  mstis :  1;  /* Multi-Master Contention Interrupt Status */
    uint32_t              : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_ISR. */
typedef volatile struct ALT_SPIM_ISR_s  ALT_SPIM_ISR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_ISR register from the beginning of the component. */
#define ALT_SPIM_ISR_OFST        0x30
/* The address of the ALT_SPIM_ISR register. */
#define ALT_SPIM_ISR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_ISR_OFST))

/*
 * Register : Raw Interrupt Status Register - risr
 * 
 * This register reports the status of the SPI Master interrupts prior to masking.
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
 *  ALT_SPIM_RISR_TXEIR_E_INACT | 0x0   | spi_txe_intr interrupt is not active prior to 
 * :                            |       | masking                                       
 *  ALT_SPIM_RISR_TXEIR_E_ACT   | 0x1   | spi_txe_intr interrupt is active prior masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_RISR_TXEIR
 * 
 * spi_txe_intr interrupt is not active prior to masking
 */
#define ALT_SPIM_RISR_TXEIR_E_INACT 0x0
/*
 * Enumerated value for register field ALT_SPIM_RISR_TXEIR
 * 
 * spi_txe_intr interrupt is active prior masking
 */
#define ALT_SPIM_RISR_TXEIR_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_RISR_TXEIR register field. */
#define ALT_SPIM_RISR_TXEIR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_RISR_TXEIR register field. */
#define ALT_SPIM_RISR_TXEIR_MSB        0
/* The width in bits of the ALT_SPIM_RISR_TXEIR register field. */
#define ALT_SPIM_RISR_TXEIR_WIDTH      1
/* The mask used to set the ALT_SPIM_RISR_TXEIR register field value. */
#define ALT_SPIM_RISR_TXEIR_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIM_RISR_TXEIR register field value. */
#define ALT_SPIM_RISR_TXEIR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIM_RISR_TXEIR register field. */
#define ALT_SPIM_RISR_TXEIR_RESET      0x0
/* Extracts the ALT_SPIM_RISR_TXEIR field value from a register. */
#define ALT_SPIM_RISR_TXEIR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIM_RISR_TXEIR register field value suitable for setting the register. */
#define ALT_SPIM_RISR_TXEIR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Transmit FIFO Overflow Raw Interrupt Status - txoir
 * 
 * The interrupt is active or inactive prior to masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                                   
 * :----------------------------|:------|:-----------------------------------------------
 *  ALT_SPIM_RISR_TXOIR_E_INACT | 0x0   | spi_txo_intr interrupt is not active prior to 
 * :                            |       | masking                                       
 *  ALT_SPIM_RISR_TXOIR_E_ACT   | 0x1   | spi_txo_intr interrupt is active prior masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_RISR_TXOIR
 * 
 * spi_txo_intr interrupt is not active prior to masking
 */
#define ALT_SPIM_RISR_TXOIR_E_INACT 0x0
/*
 * Enumerated value for register field ALT_SPIM_RISR_TXOIR
 * 
 * spi_txo_intr interrupt is active prior masking
 */
#define ALT_SPIM_RISR_TXOIR_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_RISR_TXOIR register field. */
#define ALT_SPIM_RISR_TXOIR_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SPIM_RISR_TXOIR register field. */
#define ALT_SPIM_RISR_TXOIR_MSB        1
/* The width in bits of the ALT_SPIM_RISR_TXOIR register field. */
#define ALT_SPIM_RISR_TXOIR_WIDTH      1
/* The mask used to set the ALT_SPIM_RISR_TXOIR register field value. */
#define ALT_SPIM_RISR_TXOIR_SET_MSK    0x00000002
/* The mask used to clear the ALT_SPIM_RISR_TXOIR register field value. */
#define ALT_SPIM_RISR_TXOIR_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SPIM_RISR_TXOIR register field. */
#define ALT_SPIM_RISR_TXOIR_RESET      0x0
/* Extracts the ALT_SPIM_RISR_TXOIR field value from a register. */
#define ALT_SPIM_RISR_TXOIR_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SPIM_RISR_TXOIR register field value suitable for setting the register. */
#define ALT_SPIM_RISR_TXOIR_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Receive FIFO Underflow Raw Interrupt Status - rxuir
 * 
 * The interrupt is active or inactive prior to masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                                  
 * :----------------------------|:------|:----------------------------------------------
 *  ALT_SPIM_RISR_RXUIR_E_INACT | 0x0   | spi_rxu_intr interrupt is not active prior to
 * :                            |       | masking                                      
 *  ALT_SPIM_RISR_RXUIR_E_ACT   | 0x1   | spi_rxu_intr interrupt is active prior to    
 * :                            |       | masking                                      
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_RISR_RXUIR
 * 
 * spi_rxu_intr interrupt is not active prior to masking
 */
#define ALT_SPIM_RISR_RXUIR_E_INACT 0x0
/*
 * Enumerated value for register field ALT_SPIM_RISR_RXUIR
 * 
 * spi_rxu_intr interrupt is active prior to masking
 */
#define ALT_SPIM_RISR_RXUIR_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_RISR_RXUIR register field. */
#define ALT_SPIM_RISR_RXUIR_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SPIM_RISR_RXUIR register field. */
#define ALT_SPIM_RISR_RXUIR_MSB        2
/* The width in bits of the ALT_SPIM_RISR_RXUIR register field. */
#define ALT_SPIM_RISR_RXUIR_WIDTH      1
/* The mask used to set the ALT_SPIM_RISR_RXUIR register field value. */
#define ALT_SPIM_RISR_RXUIR_SET_MSK    0x00000004
/* The mask used to clear the ALT_SPIM_RISR_RXUIR register field value. */
#define ALT_SPIM_RISR_RXUIR_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SPIM_RISR_RXUIR register field. */
#define ALT_SPIM_RISR_RXUIR_RESET      0x0
/* Extracts the ALT_SPIM_RISR_RXUIR field value from a register. */
#define ALT_SPIM_RISR_RXUIR_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SPIM_RISR_RXUIR register field value suitable for setting the register. */
#define ALT_SPIM_RISR_RXUIR_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Receive FIFO Overflow Raw Interrupt Status - rxoir
 * 
 * The interrupt is active or inactive prior to masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description                                   
 * :-------------------------------|:------|:-----------------------------------------------
 *  ALT_SPIM_RISR_RXOIR_E_INACTOVE | 0x0   | spi_rxo_intr interrupt is not active prior to 
 * :                               |       | masking                                       
 *  ALT_SPIM_RISR_RXOIR_E_ACT      | 0x1   | spi_rxo_intr interrupt is active prior masking
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_RISR_RXOIR
 * 
 * spi_rxo_intr interrupt is not active prior to masking
 */
#define ALT_SPIM_RISR_RXOIR_E_INACTOVE  0x0
/*
 * Enumerated value for register field ALT_SPIM_RISR_RXOIR
 * 
 * spi_rxo_intr interrupt is active prior masking
 */
#define ALT_SPIM_RISR_RXOIR_E_ACT       0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_RISR_RXOIR register field. */
#define ALT_SPIM_RISR_RXOIR_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SPIM_RISR_RXOIR register field. */
#define ALT_SPIM_RISR_RXOIR_MSB        3
/* The width in bits of the ALT_SPIM_RISR_RXOIR register field. */
#define ALT_SPIM_RISR_RXOIR_WIDTH      1
/* The mask used to set the ALT_SPIM_RISR_RXOIR register field value. */
#define ALT_SPIM_RISR_RXOIR_SET_MSK    0x00000008
/* The mask used to clear the ALT_SPIM_RISR_RXOIR register field value. */
#define ALT_SPIM_RISR_RXOIR_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SPIM_RISR_RXOIR register field. */
#define ALT_SPIM_RISR_RXOIR_RESET      0x0
/* Extracts the ALT_SPIM_RISR_RXOIR field value from a register. */
#define ALT_SPIM_RISR_RXOIR_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SPIM_RISR_RXOIR register field value suitable for setting the register. */
#define ALT_SPIM_RISR_RXOIR_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Receive FIFO Full Raw Interrupt Status - rxfir
 * 
 * The interrupt is active or inactive prior to masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                                  
 * :----------------------------|:------|:----------------------------------------------
 *  ALT_SPIM_RISR_RXFIR_E_INACT | 0x0   | spi_rxf_intr interrupt is not active prior to
 * :                            |       | masking                                      
 *  ALT_SPIM_RISR_RXFIR_E_ACT   | 0x1   | spi_rxf_intr interrupt is active prior to    
 * :                            |       | masking                                      
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_RISR_RXFIR
 * 
 * spi_rxf_intr interrupt is not active prior to masking
 */
#define ALT_SPIM_RISR_RXFIR_E_INACT 0x0
/*
 * Enumerated value for register field ALT_SPIM_RISR_RXFIR
 * 
 * spi_rxf_intr interrupt is active prior to masking
 */
#define ALT_SPIM_RISR_RXFIR_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_RISR_RXFIR register field. */
#define ALT_SPIM_RISR_RXFIR_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SPIM_RISR_RXFIR register field. */
#define ALT_SPIM_RISR_RXFIR_MSB        4
/* The width in bits of the ALT_SPIM_RISR_RXFIR register field. */
#define ALT_SPIM_RISR_RXFIR_WIDTH      1
/* The mask used to set the ALT_SPIM_RISR_RXFIR register field value. */
#define ALT_SPIM_RISR_RXFIR_SET_MSK    0x00000010
/* The mask used to clear the ALT_SPIM_RISR_RXFIR register field value. */
#define ALT_SPIM_RISR_RXFIR_CLR_MSK    0xffffffef
/* The reset value of the ALT_SPIM_RISR_RXFIR register field. */
#define ALT_SPIM_RISR_RXFIR_RESET      0x0
/* Extracts the ALT_SPIM_RISR_RXFIR field value from a register. */
#define ALT_SPIM_RISR_RXFIR_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SPIM_RISR_RXFIR register field value suitable for setting the register. */
#define ALT_SPIM_RISR_RXFIR_SET(value) (((value) << 4) & 0x00000010)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_RISR.
 */
struct ALT_SPIM_RISR_s
{
    const uint32_t  txeir :  1;  /* Transmit FIFO Empty Raw Interrupt Status */
    const uint32_t  txoir :  1;  /* Transmit FIFO Overflow Raw Interrupt Status */
    const uint32_t  rxuir :  1;  /* Receive FIFO Underflow Raw Interrupt Status */
    const uint32_t  rxoir :  1;  /* Receive FIFO Overflow Raw Interrupt Status */
    const uint32_t  rxfir :  1;  /* Receive FIFO Full Raw Interrupt Status */
    uint32_t              : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_RISR. */
typedef volatile struct ALT_SPIM_RISR_s  ALT_SPIM_RISR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_RISR register from the beginning of the component. */
#define ALT_SPIM_RISR_OFST        0x34
/* The address of the ALT_SPIM_RISR register. */
#define ALT_SPIM_RISR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_RISR_OFST))

/*
 * Register : Transmit FIFO Overflow Interrupt Clear Register - txoicr
 * 
 * Transmit FIFO Overflow Interrupt Clear Register
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
 * clears the spi_txo_intr interrupt; writing has no effect.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIM_TXOICR_TXOICR register field. */
#define ALT_SPIM_TXOICR_TXOICR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_TXOICR_TXOICR register field. */
#define ALT_SPIM_TXOICR_TXOICR_MSB        0
/* The width in bits of the ALT_SPIM_TXOICR_TXOICR register field. */
#define ALT_SPIM_TXOICR_TXOICR_WIDTH      1
/* The mask used to set the ALT_SPIM_TXOICR_TXOICR register field value. */
#define ALT_SPIM_TXOICR_TXOICR_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIM_TXOICR_TXOICR register field value. */
#define ALT_SPIM_TXOICR_TXOICR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIM_TXOICR_TXOICR register field. */
#define ALT_SPIM_TXOICR_TXOICR_RESET      0x0
/* Extracts the ALT_SPIM_TXOICR_TXOICR field value from a register. */
#define ALT_SPIM_TXOICR_TXOICR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIM_TXOICR_TXOICR register field value suitable for setting the register. */
#define ALT_SPIM_TXOICR_TXOICR_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_TXOICR.
 */
struct ALT_SPIM_TXOICR_s
{
    const uint32_t  txoicr :  1;  /* Clear Transmit FIFO Overflow Interrupt */
    uint32_t               : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_TXOICR. */
typedef volatile struct ALT_SPIM_TXOICR_s  ALT_SPIM_TXOICR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_TXOICR register from the beginning of the component. */
#define ALT_SPIM_TXOICR_OFST        0x38
/* The address of the ALT_SPIM_TXOICR register. */
#define ALT_SPIM_TXOICR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_TXOICR_OFST))

/*
 * Register : Receive FIFO Overflow Interrupt Clear Register - rxoicr
 * 
 * Receive FIFO Overflow Interrupt Clear Register
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
 * clears the spi_rxo_intr interrupt; writing has no effect.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIM_RXOICR_RXOICR register field. */
#define ALT_SPIM_RXOICR_RXOICR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_RXOICR_RXOICR register field. */
#define ALT_SPIM_RXOICR_RXOICR_MSB        0
/* The width in bits of the ALT_SPIM_RXOICR_RXOICR register field. */
#define ALT_SPIM_RXOICR_RXOICR_WIDTH      1
/* The mask used to set the ALT_SPIM_RXOICR_RXOICR register field value. */
#define ALT_SPIM_RXOICR_RXOICR_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIM_RXOICR_RXOICR register field value. */
#define ALT_SPIM_RXOICR_RXOICR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIM_RXOICR_RXOICR register field. */
#define ALT_SPIM_RXOICR_RXOICR_RESET      0x0
/* Extracts the ALT_SPIM_RXOICR_RXOICR field value from a register. */
#define ALT_SPIM_RXOICR_RXOICR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIM_RXOICR_RXOICR register field value suitable for setting the register. */
#define ALT_SPIM_RXOICR_RXOICR_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_RXOICR.
 */
struct ALT_SPIM_RXOICR_s
{
    const uint32_t  rxoicr :  1;  /* Clear Receive FIFO Overflow Interrupt */
    uint32_t               : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_RXOICR. */
typedef volatile struct ALT_SPIM_RXOICR_s  ALT_SPIM_RXOICR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_RXOICR register from the beginning of the component. */
#define ALT_SPIM_RXOICR_OFST        0x3c
/* The address of the ALT_SPIM_RXOICR register. */
#define ALT_SPIM_RXOICR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_RXOICR_OFST))

/*
 * Register : Receive FIFO Underflow Interrupt Clear Register - rxuicr
 * 
 * Receive FIFO Underflow Interrupt Clear Register
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
 * clears the spi_rxu_intr interrupt; writing has no effect.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIM_RXUICR_RXUICR register field. */
#define ALT_SPIM_RXUICR_RXUICR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_RXUICR_RXUICR register field. */
#define ALT_SPIM_RXUICR_RXUICR_MSB        0
/* The width in bits of the ALT_SPIM_RXUICR_RXUICR register field. */
#define ALT_SPIM_RXUICR_RXUICR_WIDTH      1
/* The mask used to set the ALT_SPIM_RXUICR_RXUICR register field value. */
#define ALT_SPIM_RXUICR_RXUICR_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIM_RXUICR_RXUICR register field value. */
#define ALT_SPIM_RXUICR_RXUICR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIM_RXUICR_RXUICR register field. */
#define ALT_SPIM_RXUICR_RXUICR_RESET      0x0
/* Extracts the ALT_SPIM_RXUICR_RXUICR field value from a register. */
#define ALT_SPIM_RXUICR_RXUICR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIM_RXUICR_RXUICR register field value suitable for setting the register. */
#define ALT_SPIM_RXUICR_RXUICR_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_RXUICR.
 */
struct ALT_SPIM_RXUICR_s
{
    const uint32_t  rxuicr :  1;  /* Clear Receive FIFO Underflow Interrupt */
    uint32_t               : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_RXUICR. */
typedef volatile struct ALT_SPIM_RXUICR_s  ALT_SPIM_RXUICR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_RXUICR register from the beginning of the component. */
#define ALT_SPIM_RXUICR_OFST        0x40
/* The address of the ALT_SPIM_RXUICR register. */
#define ALT_SPIM_RXUICR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_RXUICR_OFST))

/*
 * Register : Interrupt Clear Register - icr
 * 
 * Clear Interrupt
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description    
 * :-------|:-------|:------|:----------------
 *  [0]    | R      | 0x0   | Clear Interrupt
 *  [31:1] | ???    | 0x0   | *UNDEFINED*    
 * 
 */
/*
 * Field : Clear Interrupt - icr
 * 
 * This register is set if any of the interrupts are active. A read clears the
 * spi_txo_intr, spi_rxu_intr, spi_rxo_intr, and the spi_mst_intr interrupts.
 * Writing to this register has no effect.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIM_ICR_ICR register field. */
#define ALT_SPIM_ICR_ICR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_ICR_ICR register field. */
#define ALT_SPIM_ICR_ICR_MSB        0
/* The width in bits of the ALT_SPIM_ICR_ICR register field. */
#define ALT_SPIM_ICR_ICR_WIDTH      1
/* The mask used to set the ALT_SPIM_ICR_ICR register field value. */
#define ALT_SPIM_ICR_ICR_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIM_ICR_ICR register field value. */
#define ALT_SPIM_ICR_ICR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIM_ICR_ICR register field. */
#define ALT_SPIM_ICR_ICR_RESET      0x0
/* Extracts the ALT_SPIM_ICR_ICR field value from a register. */
#define ALT_SPIM_ICR_ICR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIM_ICR_ICR register field value suitable for setting the register. */
#define ALT_SPIM_ICR_ICR_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_ICR.
 */
struct ALT_SPIM_ICR_s
{
    const uint32_t  icr :  1;  /* Clear Interrupt */
    uint32_t            : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_ICR. */
typedef volatile struct ALT_SPIM_ICR_s  ALT_SPIM_ICR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_ICR register from the beginning of the component. */
#define ALT_SPIM_ICR_OFST        0x48
/* The address of the ALT_SPIM_ICR register. */
#define ALT_SPIM_ICR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_ICR_OFST))

/*
 * Register : DMA Control Register - dmacr
 * 
 * This register is used to enable the DMA Controller interface operation.
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
 * This bit enables/disables the receive FIFO DMA channel.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description         
 * :----------------------------|:------|:---------------------
 *  ALT_SPIM_DMACR_RDMAE_E_DISD | 0x0   | Receive DMA disabled
 *  ALT_SPIM_DMACR_RDMAE_E_END  | 0x1   | Receive DMA enabled 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_DMACR_RDMAE
 * 
 * Receive DMA disabled
 */
#define ALT_SPIM_DMACR_RDMAE_E_DISD 0x0
/*
 * Enumerated value for register field ALT_SPIM_DMACR_RDMAE
 * 
 * Receive DMA enabled
 */
#define ALT_SPIM_DMACR_RDMAE_E_END  0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_DMACR_RDMAE register field. */
#define ALT_SPIM_DMACR_RDMAE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_DMACR_RDMAE register field. */
#define ALT_SPIM_DMACR_RDMAE_MSB        0
/* The width in bits of the ALT_SPIM_DMACR_RDMAE register field. */
#define ALT_SPIM_DMACR_RDMAE_WIDTH      1
/* The mask used to set the ALT_SPIM_DMACR_RDMAE register field value. */
#define ALT_SPIM_DMACR_RDMAE_SET_MSK    0x00000001
/* The mask used to clear the ALT_SPIM_DMACR_RDMAE register field value. */
#define ALT_SPIM_DMACR_RDMAE_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SPIM_DMACR_RDMAE register field. */
#define ALT_SPIM_DMACR_RDMAE_RESET      0x0
/* Extracts the ALT_SPIM_DMACR_RDMAE field value from a register. */
#define ALT_SPIM_DMACR_RDMAE_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SPIM_DMACR_RDMAE register field value suitable for setting the register. */
#define ALT_SPIM_DMACR_RDMAE_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Transmit DMA Enable - tdmae
 * 
 * This bit enables/disables the transmit FIFO DMA channel.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description          
 * :----------------------------|:------|:----------------------
 *  ALT_SPIM_DMACR_TDMAE_E_DISD | 0x0   | Transmit DMA disabled
 *  ALT_SPIM_DMACR_TDMAE_E_END  | 0x1   | Transmit DMA enabled 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SPIM_DMACR_TDMAE
 * 
 * Transmit DMA disabled
 */
#define ALT_SPIM_DMACR_TDMAE_E_DISD 0x0
/*
 * Enumerated value for register field ALT_SPIM_DMACR_TDMAE
 * 
 * Transmit DMA enabled
 */
#define ALT_SPIM_DMACR_TDMAE_E_END  0x1

/* The Least Significant Bit (LSB) position of the ALT_SPIM_DMACR_TDMAE register field. */
#define ALT_SPIM_DMACR_TDMAE_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SPIM_DMACR_TDMAE register field. */
#define ALT_SPIM_DMACR_TDMAE_MSB        1
/* The width in bits of the ALT_SPIM_DMACR_TDMAE register field. */
#define ALT_SPIM_DMACR_TDMAE_WIDTH      1
/* The mask used to set the ALT_SPIM_DMACR_TDMAE register field value. */
#define ALT_SPIM_DMACR_TDMAE_SET_MSK    0x00000002
/* The mask used to clear the ALT_SPIM_DMACR_TDMAE register field value. */
#define ALT_SPIM_DMACR_TDMAE_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SPIM_DMACR_TDMAE register field. */
#define ALT_SPIM_DMACR_TDMAE_RESET      0x0
/* Extracts the ALT_SPIM_DMACR_TDMAE field value from a register. */
#define ALT_SPIM_DMACR_TDMAE_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SPIM_DMACR_TDMAE register field value suitable for setting the register. */
#define ALT_SPIM_DMACR_TDMAE_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_DMACR.
 */
struct ALT_SPIM_DMACR_s
{
    uint32_t  rdmae :  1;  /* Receive DMA Enable */
    uint32_t  tdmae :  1;  /* Transmit DMA Enable */
    uint32_t        : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_DMACR. */
typedef volatile struct ALT_SPIM_DMACR_s  ALT_SPIM_DMACR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_DMACR register from the beginning of the component. */
#define ALT_SPIM_DMACR_OFST        0x4c
/* The address of the ALT_SPIM_DMACR register. */
#define ALT_SPIM_DMACR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_DMACR_OFST))

/*
 * Register : DMA Transmit Data Level Register - dmatdlr
 * 
 * Controls the FIFO Level for a DMA transmit request
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
/* The Least Significant Bit (LSB) position of the ALT_SPIM_DMATDLR_DMATDL register field. */
#define ALT_SPIM_DMATDLR_DMATDL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_DMATDLR_DMATDL register field. */
#define ALT_SPIM_DMATDLR_DMATDL_MSB        7
/* The width in bits of the ALT_SPIM_DMATDLR_DMATDL register field. */
#define ALT_SPIM_DMATDLR_DMATDL_WIDTH      8
/* The mask used to set the ALT_SPIM_DMATDLR_DMATDL register field value. */
#define ALT_SPIM_DMATDLR_DMATDL_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SPIM_DMATDLR_DMATDL register field value. */
#define ALT_SPIM_DMATDLR_DMATDL_CLR_MSK    0xffffff00
/* The reset value of the ALT_SPIM_DMATDLR_DMATDL register field. */
#define ALT_SPIM_DMATDLR_DMATDL_RESET      0x0
/* Extracts the ALT_SPIM_DMATDLR_DMATDL field value from a register. */
#define ALT_SPIM_DMATDLR_DMATDL_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SPIM_DMATDLR_DMATDL register field value suitable for setting the register. */
#define ALT_SPIM_DMATDLR_DMATDL_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_DMATDLR.
 */
struct ALT_SPIM_DMATDLR_s
{
    uint32_t  dmatdl :  8;  /* Transmit Data Level */
    uint32_t         : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_DMATDLR. */
typedef volatile struct ALT_SPIM_DMATDLR_s  ALT_SPIM_DMATDLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_DMATDLR register from the beginning of the component. */
#define ALT_SPIM_DMATDLR_OFST        0x50
/* The address of the ALT_SPIM_DMATDLR register. */
#define ALT_SPIM_DMATDLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_DMATDLR_OFST))

/*
 * Register : DMA Receive Data Level Register - dmardlr
 * 
 * Controls the FIFO Level for a DMA receeive request
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
/* The Least Significant Bit (LSB) position of the ALT_SPIM_DMARDLR_DMARDL register field. */
#define ALT_SPIM_DMARDLR_DMARDL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_DMARDLR_DMARDL register field. */
#define ALT_SPIM_DMARDLR_DMARDL_MSB        7
/* The width in bits of the ALT_SPIM_DMARDLR_DMARDL register field. */
#define ALT_SPIM_DMARDLR_DMARDL_WIDTH      8
/* The mask used to set the ALT_SPIM_DMARDLR_DMARDL register field value. */
#define ALT_SPIM_DMARDLR_DMARDL_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SPIM_DMARDLR_DMARDL register field value. */
#define ALT_SPIM_DMARDLR_DMARDL_CLR_MSK    0xffffff00
/* The reset value of the ALT_SPIM_DMARDLR_DMARDL register field. */
#define ALT_SPIM_DMARDLR_DMARDL_RESET      0x0
/* Extracts the ALT_SPIM_DMARDLR_DMARDL field value from a register. */
#define ALT_SPIM_DMARDLR_DMARDL_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SPIM_DMARDLR_DMARDL register field value suitable for setting the register. */
#define ALT_SPIM_DMARDLR_DMARDL_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_DMARDLR.
 */
struct ALT_SPIM_DMARDLR_s
{
    uint32_t  dmardl :  8;  /* Receive Data Level */
    uint32_t         : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_DMARDLR. */
typedef volatile struct ALT_SPIM_DMARDLR_s  ALT_SPIM_DMARDLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_DMARDLR register from the beginning of the component. */
#define ALT_SPIM_DMARDLR_OFST        0x54
/* The address of the ALT_SPIM_DMARDLR register. */
#define ALT_SPIM_DMARDLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_DMARDLR_OFST))

/*
 * Register : Identification Register - idr
 * 
 * This register contains the peripherals identification code, which is 0x05510000.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset     | Description            
 * :-------|:-------|:----------|:------------------------
 *  [31:0] | R      | 0x5510000 | Identification Register
 * 
 */
/*
 * Field : Identification Register - idr
 * 
 * This register contains the peripherals identification code
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIM_IDR_IDR register field. */
#define ALT_SPIM_IDR_IDR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_IDR_IDR register field. */
#define ALT_SPIM_IDR_IDR_MSB        31
/* The width in bits of the ALT_SPIM_IDR_IDR register field. */
#define ALT_SPIM_IDR_IDR_WIDTH      32
/* The mask used to set the ALT_SPIM_IDR_IDR register field value. */
#define ALT_SPIM_IDR_IDR_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SPIM_IDR_IDR register field value. */
#define ALT_SPIM_IDR_IDR_CLR_MSK    0x00000000
/* The reset value of the ALT_SPIM_IDR_IDR register field. */
#define ALT_SPIM_IDR_IDR_RESET      0x5510000
/* Extracts the ALT_SPIM_IDR_IDR field value from a register. */
#define ALT_SPIM_IDR_IDR_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SPIM_IDR_IDR register field value suitable for setting the register. */
#define ALT_SPIM_IDR_IDR_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_IDR.
 */
struct ALT_SPIM_IDR_s
{
    const uint32_t  idr : 32;  /* Identification Register */
};

/* The typedef declaration for register ALT_SPIM_IDR. */
typedef volatile struct ALT_SPIM_IDR_s  ALT_SPIM_IDR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_IDR register from the beginning of the component. */
#define ALT_SPIM_IDR_OFST        0x58
/* The address of the ALT_SPIM_IDR register. */
#define ALT_SPIM_IDR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_IDR_OFST))

/*
 * Register : Component Version Register - spi_version_id
 * 
 * Version ID Register value
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset      | Description    
 * :-------|:-------|:-----------|:----------------
 *  [31:0] | RW     | 0x3332302a | Version ID Code
 * 
 */
/*
 * Field : Version ID Code - spi_version_id
 * 
 * Contains the hex representation of the Synopsys component version. Consists of
 * ASCII value for each number in the version.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIM_SPI_VER_ID_SPI_VER_ID register field. */
#define ALT_SPIM_SPI_VER_ID_SPI_VER_ID_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_SPI_VER_ID_SPI_VER_ID register field. */
#define ALT_SPIM_SPI_VER_ID_SPI_VER_ID_MSB        31
/* The width in bits of the ALT_SPIM_SPI_VER_ID_SPI_VER_ID register field. */
#define ALT_SPIM_SPI_VER_ID_SPI_VER_ID_WIDTH      32
/* The mask used to set the ALT_SPIM_SPI_VER_ID_SPI_VER_ID register field value. */
#define ALT_SPIM_SPI_VER_ID_SPI_VER_ID_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SPIM_SPI_VER_ID_SPI_VER_ID register field value. */
#define ALT_SPIM_SPI_VER_ID_SPI_VER_ID_CLR_MSK    0x00000000
/* The reset value of the ALT_SPIM_SPI_VER_ID_SPI_VER_ID register field. */
#define ALT_SPIM_SPI_VER_ID_SPI_VER_ID_RESET      0x3332302a
/* Extracts the ALT_SPIM_SPI_VER_ID_SPI_VER_ID field value from a register. */
#define ALT_SPIM_SPI_VER_ID_SPI_VER_ID_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SPIM_SPI_VER_ID_SPI_VER_ID register field value suitable for setting the register. */
#define ALT_SPIM_SPI_VER_ID_SPI_VER_ID_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_SPI_VER_ID.
 */
struct ALT_SPIM_SPI_VER_ID_s
{
    uint32_t  spi_version_id : 32;  /* Version ID Code */
};

/* The typedef declaration for register ALT_SPIM_SPI_VER_ID. */
typedef volatile struct ALT_SPIM_SPI_VER_ID_s  ALT_SPIM_SPI_VER_ID_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_SPI_VER_ID register from the beginning of the component. */
#define ALT_SPIM_SPI_VER_ID_OFST        0x5c
/* The address of the ALT_SPIM_SPI_VER_ID register. */
#define ALT_SPIM_SPI_VER_ID_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_SPI_VER_ID_OFST))

/*
 * Register : Data Register - dr
 * 
 * This register is a 16-bit read/write buffer for the transmit/receive FIFOs. When
 * the register is read, data in the receive FIFO buffer is accessed. When it is
 * written to, data are moved into the transmit FIFO buffer; a write can occur only
 * when SPI_EN = 1. FIFOs are reset when SPI_EN = 0.
 * 
 * The data register occupies 36 32-bit locations in the address map (0x60 to
 * 0xec). These are all aliases for the same data register. This is done to support
 * burst accesses.
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
/* The Least Significant Bit (LSB) position of the ALT_SPIM_DR_DR register field. */
#define ALT_SPIM_DR_DR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_DR_DR register field. */
#define ALT_SPIM_DR_DR_MSB        15
/* The width in bits of the ALT_SPIM_DR_DR register field. */
#define ALT_SPIM_DR_DR_WIDTH      16
/* The mask used to set the ALT_SPIM_DR_DR register field value. */
#define ALT_SPIM_DR_DR_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_SPIM_DR_DR register field value. */
#define ALT_SPIM_DR_DR_CLR_MSK    0xffff0000
/* The reset value of the ALT_SPIM_DR_DR register field. */
#define ALT_SPIM_DR_DR_RESET      0x0
/* Extracts the ALT_SPIM_DR_DR field value from a register. */
#define ALT_SPIM_DR_DR_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_SPIM_DR_DR register field value suitable for setting the register. */
#define ALT_SPIM_DR_DR_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_DR.
 */
struct ALT_SPIM_DR_s
{
    uint32_t  dr : 16;  /* Data */
    uint32_t     : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_DR. */
typedef volatile struct ALT_SPIM_DR_s  ALT_SPIM_DR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_DR register from the beginning of the component. */
#define ALT_SPIM_DR_OFST        0x60
/* The address of the ALT_SPIM_DR register. */
#define ALT_SPIM_DR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_DR_OFST))

/*
 * Register : RX Sample Delay Register - rx_sample_dly
 * 
 * This register controls the number of spi_m_clk cycles that are delayed (from the
 * default sample time) before the actual sample of the rxd input occurs. It is
 * impossible to write to this register when the SPI Master is enabled. The SPI
 * Master is enabled and disabled by writing to the SPIENR register.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description              
 * :-------|:-------|:------|:--------------------------
 *  [6:0]  | RW     | 0x0   | Receive Data Sample Delay
 *  [31:7] | ???    | 0x0   | *UNDEFINED*              
 * 
 */
/*
 * Field : Receive Data Sample Delay - rsd
 * 
 * This register is used to delay the sample of the rxd input port. Each value
 * represents a single spi_m_clk delay on the sample of rxd.
 * 
 * Note; If this register is programmed with a value that exceeds 64, a 0 delay
 * will be applied to the receive sample. The maximum delay is 64 spi_m_clk cycles.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SPIM_RX_SMPL_DLY_RSD register field. */
#define ALT_SPIM_RX_SMPL_DLY_RSD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SPIM_RX_SMPL_DLY_RSD register field. */
#define ALT_SPIM_RX_SMPL_DLY_RSD_MSB        6
/* The width in bits of the ALT_SPIM_RX_SMPL_DLY_RSD register field. */
#define ALT_SPIM_RX_SMPL_DLY_RSD_WIDTH      7
/* The mask used to set the ALT_SPIM_RX_SMPL_DLY_RSD register field value. */
#define ALT_SPIM_RX_SMPL_DLY_RSD_SET_MSK    0x0000007f
/* The mask used to clear the ALT_SPIM_RX_SMPL_DLY_RSD register field value. */
#define ALT_SPIM_RX_SMPL_DLY_RSD_CLR_MSK    0xffffff80
/* The reset value of the ALT_SPIM_RX_SMPL_DLY_RSD register field. */
#define ALT_SPIM_RX_SMPL_DLY_RSD_RESET      0x0
/* Extracts the ALT_SPIM_RX_SMPL_DLY_RSD field value from a register. */
#define ALT_SPIM_RX_SMPL_DLY_RSD_GET(value) (((value) & 0x0000007f) >> 0)
/* Produces a ALT_SPIM_RX_SMPL_DLY_RSD register field value suitable for setting the register. */
#define ALT_SPIM_RX_SMPL_DLY_RSD_SET(value) (((value) << 0) & 0x0000007f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SPIM_RX_SMPL_DLY.
 */
struct ALT_SPIM_RX_SMPL_DLY_s
{
    uint32_t  rsd :  7;  /* Receive Data Sample Delay */
    uint32_t      : 25;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SPIM_RX_SMPL_DLY. */
typedef volatile struct ALT_SPIM_RX_SMPL_DLY_s  ALT_SPIM_RX_SMPL_DLY_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SPIM_RX_SMPL_DLY register from the beginning of the component. */
#define ALT_SPIM_RX_SMPL_DLY_OFST        0xfc
/* The address of the ALT_SPIM_RX_SMPL_DLY register. */
#define ALT_SPIM_RX_SMPL_DLY_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SPIM_RX_SMPL_DLY_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_SPIM.
 */
struct ALT_SPIM_s
{
    volatile ALT_SPIM_CTLR0_t        ctrlr0;              /* ALT_SPIM_CTLR0 */
    volatile ALT_SPIM_CTLR1_t        ctrlr1;              /* ALT_SPIM_CTLR1 */
    volatile ALT_SPIM_SPIENR_t       spienr;              /* ALT_SPIM_SPIENR */
    volatile ALT_SPIM_MWCR_t         mwcr;                /* ALT_SPIM_MWCR */
    volatile ALT_SPIM_SER_t          ser;                 /* ALT_SPIM_SER */
    volatile ALT_SPIM_BAUDR_t        baudr;               /* ALT_SPIM_BAUDR */
    volatile ALT_SPIM_TXFTLR_t       txftlr;              /* ALT_SPIM_TXFTLR */
    volatile ALT_SPIM_RXFTLR_t       rxftlr;              /* ALT_SPIM_RXFTLR */
    volatile ALT_SPIM_TXFLR_t        txflr;               /* ALT_SPIM_TXFLR */
    volatile ALT_SPIM_RXFLR_t        rxflr;               /* ALT_SPIM_RXFLR */
    volatile ALT_SPIM_SR_t           sr;                  /* ALT_SPIM_SR */
    volatile ALT_SPIM_IMR_t          imr;                 /* ALT_SPIM_IMR */
    volatile ALT_SPIM_ISR_t          isr;                 /* ALT_SPIM_ISR */
    volatile ALT_SPIM_RISR_t         risr;                /* ALT_SPIM_RISR */
    volatile ALT_SPIM_TXOICR_t       txoicr;              /* ALT_SPIM_TXOICR */
    volatile ALT_SPIM_RXOICR_t       rxoicr;              /* ALT_SPIM_RXOICR */
    volatile ALT_SPIM_RXUICR_t       rxuicr;              /* ALT_SPIM_RXUICR */
    volatile uint32_t                _pad_0x44_0x47;      /* *UNDEFINED* */
    volatile ALT_SPIM_ICR_t          icr;                 /* ALT_SPIM_ICR */
    volatile ALT_SPIM_DMACR_t        dmacr;               /* ALT_SPIM_DMACR */
    volatile ALT_SPIM_DMATDLR_t      dmatdlr;             /* ALT_SPIM_DMATDLR */
    volatile ALT_SPIM_DMARDLR_t      dmardlr;             /* ALT_SPIM_DMARDLR */
    volatile ALT_SPIM_IDR_t          idr;                 /* ALT_SPIM_IDR */
    volatile ALT_SPIM_SPI_VER_ID_t   spi_version_id;      /* ALT_SPIM_SPI_VER_ID */
    volatile ALT_SPIM_DR_t           dr;                  /* ALT_SPIM_DR */
    volatile uint32_t                _pad_0x64_0xfb[38];  /* *UNDEFINED* */
    volatile ALT_SPIM_RX_SMPL_DLY_t  rx_sample_dly;       /* ALT_SPIM_RX_SMPL_DLY */
};

/* The typedef declaration for register group ALT_SPIM. */
typedef volatile struct ALT_SPIM_s  ALT_SPIM_t;
/* The struct declaration for the raw register contents of register group ALT_SPIM. */
struct ALT_SPIM_raw_s
{
    volatile uint32_t  ctrlr0;              /* ALT_SPIM_CTLR0 */
    volatile uint32_t  ctrlr1;              /* ALT_SPIM_CTLR1 */
    volatile uint32_t  spienr;              /* ALT_SPIM_SPIENR */
    volatile uint32_t  mwcr;                /* ALT_SPIM_MWCR */
    volatile uint32_t  ser;                 /* ALT_SPIM_SER */
    volatile uint32_t  baudr;               /* ALT_SPIM_BAUDR */
    volatile uint32_t  txftlr;              /* ALT_SPIM_TXFTLR */
    volatile uint32_t  rxftlr;              /* ALT_SPIM_RXFTLR */
    volatile uint32_t  txflr;               /* ALT_SPIM_TXFLR */
    volatile uint32_t  rxflr;               /* ALT_SPIM_RXFLR */
    volatile uint32_t  sr;                  /* ALT_SPIM_SR */
    volatile uint32_t  imr;                 /* ALT_SPIM_IMR */
    volatile uint32_t  isr;                 /* ALT_SPIM_ISR */
    volatile uint32_t  risr;                /* ALT_SPIM_RISR */
    volatile uint32_t  txoicr;              /* ALT_SPIM_TXOICR */
    volatile uint32_t  rxoicr;              /* ALT_SPIM_RXOICR */
    volatile uint32_t  rxuicr;              /* ALT_SPIM_RXUICR */
    volatile uint32_t  _pad_0x44_0x47;      /* *UNDEFINED* */
    volatile uint32_t  icr;                 /* ALT_SPIM_ICR */
    volatile uint32_t  dmacr;               /* ALT_SPIM_DMACR */
    volatile uint32_t  dmatdlr;             /* ALT_SPIM_DMATDLR */
    volatile uint32_t  dmardlr;             /* ALT_SPIM_DMARDLR */
    volatile uint32_t  idr;                 /* ALT_SPIM_IDR */
    volatile uint32_t  spi_version_id;      /* ALT_SPIM_SPI_VER_ID */
    volatile uint32_t  dr;                  /* ALT_SPIM_DR */
    volatile uint32_t  _pad_0x64_0xfb[38];  /* *UNDEFINED* */
    volatile uint32_t  rx_sample_dly;       /* ALT_SPIM_RX_SMPL_DLY */
};

/* The typedef declaration for the raw register contents of register group ALT_SPIM. */
typedef volatile struct ALT_SPIM_raw_s  ALT_SPIM_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_SPIM_H__ */

