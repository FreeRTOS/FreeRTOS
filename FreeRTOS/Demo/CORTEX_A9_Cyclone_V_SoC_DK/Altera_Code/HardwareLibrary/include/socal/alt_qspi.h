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

/* Altera - ALT_QSPI */

#ifndef __ALTERA_ALT_QSPI_H__
#define __ALTERA_ALT_QSPI_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : QSPI Flash Controller Module Registers - ALT_QSPI
 * QSPI Flash Controller Module Registers
 * 
 * Registers in the QSPI Flash Controller module accessible via its APB slave
 * 
 */
/*
 * Register : QSPI Configuration Register - cfg
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                               
 * :--------|:-------|:------|:-------------------------------------------
 *  [0]     | RW     | 0x0   | QSPI Enable                               
 *  [1]     | RW     | 0x0   | Clock Polarity                            
 *  [2]     | RW     | 0x0   | Select Clock Phase                        
 *  [6:3]   | ???    | 0x0   | *UNDEFINED*                               
 *  [7]     | RW     | 0x0   | Enable Direct Access Controller           
 *  [8]     | RW     | 0x0   | Legacy IP Mode Enable                     
 *  [9]     | RW     | 0x0   | Peripheral select decode                  
 *  [13:10] | RW     | 0x0   | Peripheral Chip Select Lines              
 *  [14]    | RW     | 0x0   | Write Protect Flash Pin                   
 *  [15]    | RW     | 0x0   | Enable DMA Peripheral Interface           
 *  [16]    | RW     | 0x0   | Enable AHB Address Re-mapping             
 *  [17]    | RW     | 0x0   | Enter XIP Mode on next READ               
 *  [18]    | RW     | 0x0   | Enter XIP Mode Immediately                
 *  [22:19] | RW     | 0xf   | Master Mode Baud Rate Divisor             
 *  [30:23] | ???    | 0x0   | *UNDEFINED*                               
 *  [31]    | R      | 0x0   | Serial interface and QSPI pipeline is IDLE
 * 
 */
/*
 * Field : QSPI Enable - en
 * 
 * If this bit is disabled, the QSPI will finish the current transfer of the data
 * word (FF_W) and stop sending. When Enabled, and qspi_n_mo_en = 0, all output
 * enables are inactive and all pins are set to input mode.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                  | Value | Description     
 * :----------------------|:------|:-----------------
 *  ALT_QSPI_CFG_EN_E_DIS | 0x0   | Disable the QSPI
 *  ALT_QSPI_CFG_EN_E_EN  | 0x1   | Enable the QSPI 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_CFG_EN
 * 
 * Disable the QSPI
 */
#define ALT_QSPI_CFG_EN_E_DIS   0x0
/*
 * Enumerated value for register field ALT_QSPI_CFG_EN
 * 
 * Enable the QSPI
 */
#define ALT_QSPI_CFG_EN_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_CFG_EN register field. */
#define ALT_QSPI_CFG_EN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_CFG_EN register field. */
#define ALT_QSPI_CFG_EN_MSB        0
/* The width in bits of the ALT_QSPI_CFG_EN register field. */
#define ALT_QSPI_CFG_EN_WIDTH      1
/* The mask used to set the ALT_QSPI_CFG_EN register field value. */
#define ALT_QSPI_CFG_EN_SET_MSK    0x00000001
/* The mask used to clear the ALT_QSPI_CFG_EN register field value. */
#define ALT_QSPI_CFG_EN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_QSPI_CFG_EN register field. */
#define ALT_QSPI_CFG_EN_RESET      0x0
/* Extracts the ALT_QSPI_CFG_EN field value from a register. */
#define ALT_QSPI_CFG_EN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_QSPI_CFG_EN register field value suitable for setting the register. */
#define ALT_QSPI_CFG_EN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Clock Polarity - selclkpol
 * 
 * Controls spiclk modes of operation.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                
 * :------------------------------|:------|:----------------------------
 *  ALT_QSPI_CFG_SELCLKPOL_E_LOW  | 0x1   | SPI clock is quiescent low 
 *  ALT_QSPI_CFG_SELCLKPOL_E_HIGH | 0x0   | SPI clock is quiescent high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_CFG_SELCLKPOL
 * 
 * SPI clock is quiescent low
 */
#define ALT_QSPI_CFG_SELCLKPOL_E_LOW    0x1
/*
 * Enumerated value for register field ALT_QSPI_CFG_SELCLKPOL
 * 
 * SPI clock is quiescent high
 */
#define ALT_QSPI_CFG_SELCLKPOL_E_HIGH   0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_CFG_SELCLKPOL register field. */
#define ALT_QSPI_CFG_SELCLKPOL_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_QSPI_CFG_SELCLKPOL register field. */
#define ALT_QSPI_CFG_SELCLKPOL_MSB        1
/* The width in bits of the ALT_QSPI_CFG_SELCLKPOL register field. */
#define ALT_QSPI_CFG_SELCLKPOL_WIDTH      1
/* The mask used to set the ALT_QSPI_CFG_SELCLKPOL register field value. */
#define ALT_QSPI_CFG_SELCLKPOL_SET_MSK    0x00000002
/* The mask used to clear the ALT_QSPI_CFG_SELCLKPOL register field value. */
#define ALT_QSPI_CFG_SELCLKPOL_CLR_MSK    0xfffffffd
/* The reset value of the ALT_QSPI_CFG_SELCLKPOL register field. */
#define ALT_QSPI_CFG_SELCLKPOL_RESET      0x0
/* Extracts the ALT_QSPI_CFG_SELCLKPOL field value from a register. */
#define ALT_QSPI_CFG_SELCLKPOL_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_QSPI_CFG_SELCLKPOL register field value suitable for setting the register. */
#define ALT_QSPI_CFG_SELCLKPOL_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Select Clock Phase - selclkphase
 * 
 * Selects whether the clock is in an active or inactive phase outside the SPI
 * word.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description               
 * :---------------------------------|:------|:---------------------------
 *  ALT_QSPI_CFG_SELCLKPHASE_E_ACT   | 0x0   | SPI clock is quiescent low
 *  ALT_QSPI_CFG_SELCLKPHASE_E_INACT | 0x1   | Clock Inactive            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_CFG_SELCLKPHASE
 * 
 * SPI clock is quiescent low
 */
#define ALT_QSPI_CFG_SELCLKPHASE_E_ACT      0x0
/*
 * Enumerated value for register field ALT_QSPI_CFG_SELCLKPHASE
 * 
 * Clock Inactive
 */
#define ALT_QSPI_CFG_SELCLKPHASE_E_INACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_CFG_SELCLKPHASE register field. */
#define ALT_QSPI_CFG_SELCLKPHASE_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_QSPI_CFG_SELCLKPHASE register field. */
#define ALT_QSPI_CFG_SELCLKPHASE_MSB        2
/* The width in bits of the ALT_QSPI_CFG_SELCLKPHASE register field. */
#define ALT_QSPI_CFG_SELCLKPHASE_WIDTH      1
/* The mask used to set the ALT_QSPI_CFG_SELCLKPHASE register field value. */
#define ALT_QSPI_CFG_SELCLKPHASE_SET_MSK    0x00000004
/* The mask used to clear the ALT_QSPI_CFG_SELCLKPHASE register field value. */
#define ALT_QSPI_CFG_SELCLKPHASE_CLR_MSK    0xfffffffb
/* The reset value of the ALT_QSPI_CFG_SELCLKPHASE register field. */
#define ALT_QSPI_CFG_SELCLKPHASE_RESET      0x0
/* Extracts the ALT_QSPI_CFG_SELCLKPHASE field value from a register. */
#define ALT_QSPI_CFG_SELCLKPHASE_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_QSPI_CFG_SELCLKPHASE register field value suitable for setting the register. */
#define ALT_QSPI_CFG_SELCLKPHASE_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Enable Direct Access Controller - endiracc
 * 
 * If disabled, the Direct Access Controller becomes inactive once the current
 * transfer of the data word (FF_W) is complete. When the Direct Access Controller
 * and Indirect Access Controller are both disabled, all AHB requests are completed
 * with an error response.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description               
 * :----------------------------|:------|:---------------------------
 *  ALT_QSPI_CFG_ENDIRACC_E_DIS | 0x0   | Disable Direct Access Ctrl
 *  ALT_QSPI_CFG_ENDIRACC_E_EN  | 0x1   | Enable Direct Access Ctrl 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_CFG_ENDIRACC
 * 
 * Disable Direct Access Ctrl
 */
#define ALT_QSPI_CFG_ENDIRACC_E_DIS 0x0
/*
 * Enumerated value for register field ALT_QSPI_CFG_ENDIRACC
 * 
 * Enable Direct Access Ctrl
 */
#define ALT_QSPI_CFG_ENDIRACC_E_EN  0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_CFG_ENDIRACC register field. */
#define ALT_QSPI_CFG_ENDIRACC_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_QSPI_CFG_ENDIRACC register field. */
#define ALT_QSPI_CFG_ENDIRACC_MSB        7
/* The width in bits of the ALT_QSPI_CFG_ENDIRACC register field. */
#define ALT_QSPI_CFG_ENDIRACC_WIDTH      1
/* The mask used to set the ALT_QSPI_CFG_ENDIRACC register field value. */
#define ALT_QSPI_CFG_ENDIRACC_SET_MSK    0x00000080
/* The mask used to clear the ALT_QSPI_CFG_ENDIRACC register field value. */
#define ALT_QSPI_CFG_ENDIRACC_CLR_MSK    0xffffff7f
/* The reset value of the ALT_QSPI_CFG_ENDIRACC register field. */
#define ALT_QSPI_CFG_ENDIRACC_RESET      0x0
/* Extracts the ALT_QSPI_CFG_ENDIRACC field value from a register. */
#define ALT_QSPI_CFG_ENDIRACC_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_QSPI_CFG_ENDIRACC register field value suitable for setting the register. */
#define ALT_QSPI_CFG_ENDIRACC_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Legacy IP Mode Enable - enlegacyip
 * 
 * This bit can select the Direct Access Controller/Indirect Access Controller or
 * legacy mode.If legacy mode is selected, any write to the controller via the AHB
 * interface is serialized and sent to the FLASH device. Any valid AHB read will
 * pop the internal RX-FIFO, retrieving data that was forwarded by the external
 * FLASH device on the SPI lines, byte transfers of 4, 2 or 1 are permitted and
 * controlled via the HSIZE input.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                          
 * :---------------------------------|:------|:--------------------------------------
 *  ALT_QSPI_CFG_ENLEGACYIP_E_LEGMOD | 0x1   | Legacy Mode                          
 *  ALT_QSPI_CFG_ENLEGACYIP_E_DIMOD  | 0x0   | Use Direct/Indirect Access Controller
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_CFG_ENLEGACYIP
 * 
 * Legacy Mode
 */
#define ALT_QSPI_CFG_ENLEGACYIP_E_LEGMOD    0x1
/*
 * Enumerated value for register field ALT_QSPI_CFG_ENLEGACYIP
 * 
 * Use Direct/Indirect Access Controller
 */
#define ALT_QSPI_CFG_ENLEGACYIP_E_DIMOD     0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_CFG_ENLEGACYIP register field. */
#define ALT_QSPI_CFG_ENLEGACYIP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_QSPI_CFG_ENLEGACYIP register field. */
#define ALT_QSPI_CFG_ENLEGACYIP_MSB        8
/* The width in bits of the ALT_QSPI_CFG_ENLEGACYIP register field. */
#define ALT_QSPI_CFG_ENLEGACYIP_WIDTH      1
/* The mask used to set the ALT_QSPI_CFG_ENLEGACYIP register field value. */
#define ALT_QSPI_CFG_ENLEGACYIP_SET_MSK    0x00000100
/* The mask used to clear the ALT_QSPI_CFG_ENLEGACYIP register field value. */
#define ALT_QSPI_CFG_ENLEGACYIP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_QSPI_CFG_ENLEGACYIP register field. */
#define ALT_QSPI_CFG_ENLEGACYIP_RESET      0x0
/* Extracts the ALT_QSPI_CFG_ENLEGACYIP field value from a register. */
#define ALT_QSPI_CFG_ENLEGACYIP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_QSPI_CFG_ENLEGACYIP register field value suitable for setting the register. */
#define ALT_QSPI_CFG_ENLEGACYIP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Peripheral select decode - perseldec
 * 
 * Select between '1 of 4 selects' or 'external 4-to-16 decode'. The
 * qspi_n_ss_out[3:0] output signals are controlled.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                      
 * :----------------------------------|:------|:----------------------------------
 *  ALT_QSPI_CFG_PERSELDEC_E_SEL4TO16 | 0x1   | Select external 4-to-16 decode   
 *  ALT_QSPI_CFG_PERSELDEC_E_SEL1OF4  | 0x0   | Selects 1 of 4 qspi_n_ss_out[3:0]
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_CFG_PERSELDEC
 * 
 * Select external 4-to-16 decode
 */
#define ALT_QSPI_CFG_PERSELDEC_E_SEL4TO16   0x1
/*
 * Enumerated value for register field ALT_QSPI_CFG_PERSELDEC
 * 
 * Selects 1 of 4 qspi_n_ss_out[3:0]
 */
#define ALT_QSPI_CFG_PERSELDEC_E_SEL1OF4    0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_CFG_PERSELDEC register field. */
#define ALT_QSPI_CFG_PERSELDEC_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_QSPI_CFG_PERSELDEC register field. */
#define ALT_QSPI_CFG_PERSELDEC_MSB        9
/* The width in bits of the ALT_QSPI_CFG_PERSELDEC register field. */
#define ALT_QSPI_CFG_PERSELDEC_WIDTH      1
/* The mask used to set the ALT_QSPI_CFG_PERSELDEC register field value. */
#define ALT_QSPI_CFG_PERSELDEC_SET_MSK    0x00000200
/* The mask used to clear the ALT_QSPI_CFG_PERSELDEC register field value. */
#define ALT_QSPI_CFG_PERSELDEC_CLR_MSK    0xfffffdff
/* The reset value of the ALT_QSPI_CFG_PERSELDEC register field. */
#define ALT_QSPI_CFG_PERSELDEC_RESET      0x0
/* Extracts the ALT_QSPI_CFG_PERSELDEC field value from a register. */
#define ALT_QSPI_CFG_PERSELDEC_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_QSPI_CFG_PERSELDEC register field value suitable for setting the register. */
#define ALT_QSPI_CFG_PERSELDEC_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Peripheral Chip Select Lines - percslines
 * 
 * Peripheral chip select line output decode type. As per perseldec, if perseldec =
 * 0, the decode is select 1 of 4 decoding on signals, qspi_n_ss_out[3:0], The
 * asserted decode line goes to 0. If perseldec = 1, the signals qspi_n_ss_out[3:0]
 * require an external 4 to 16 decoder.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_CFG_PERCSLINES register field. */
#define ALT_QSPI_CFG_PERCSLINES_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_QSPI_CFG_PERCSLINES register field. */
#define ALT_QSPI_CFG_PERCSLINES_MSB        13
/* The width in bits of the ALT_QSPI_CFG_PERCSLINES register field. */
#define ALT_QSPI_CFG_PERCSLINES_WIDTH      4
/* The mask used to set the ALT_QSPI_CFG_PERCSLINES register field value. */
#define ALT_QSPI_CFG_PERCSLINES_SET_MSK    0x00003c00
/* The mask used to clear the ALT_QSPI_CFG_PERCSLINES register field value. */
#define ALT_QSPI_CFG_PERCSLINES_CLR_MSK    0xffffc3ff
/* The reset value of the ALT_QSPI_CFG_PERCSLINES register field. */
#define ALT_QSPI_CFG_PERCSLINES_RESET      0x0
/* Extracts the ALT_QSPI_CFG_PERCSLINES field value from a register. */
#define ALT_QSPI_CFG_PERCSLINES_GET(value) (((value) & 0x00003c00) >> 10)
/* Produces a ALT_QSPI_CFG_PERCSLINES register field value suitable for setting the register. */
#define ALT_QSPI_CFG_PERCSLINES_SET(value) (((value) << 10) & 0x00003c00)

/*
 * Field : Write Protect Flash Pin - wp
 * 
 * This bit controls the write protect pin of the flash devices. The signal
 * qspi_mo2_wpn needs to be resynchronized to the generated memory clock as
 * necessary.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description          
 * :-----------------------------|:------|:----------------------
 *  ALT_QSPI_CFG_WP_E_WRPROTON   | 0x1   | Enable Write Protect 
 *  ALT_QSPI_CFG_WP_E_WRTPROTOFF | 0x0   | Disable Write Protect
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_CFG_WP
 * 
 * Enable Write Protect
 */
#define ALT_QSPI_CFG_WP_E_WRPROTON      0x1
/*
 * Enumerated value for register field ALT_QSPI_CFG_WP
 * 
 * Disable Write Protect
 */
#define ALT_QSPI_CFG_WP_E_WRTPROTOFF    0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_CFG_WP register field. */
#define ALT_QSPI_CFG_WP_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_QSPI_CFG_WP register field. */
#define ALT_QSPI_CFG_WP_MSB        14
/* The width in bits of the ALT_QSPI_CFG_WP register field. */
#define ALT_QSPI_CFG_WP_WIDTH      1
/* The mask used to set the ALT_QSPI_CFG_WP register field value. */
#define ALT_QSPI_CFG_WP_SET_MSK    0x00004000
/* The mask used to clear the ALT_QSPI_CFG_WP register field value. */
#define ALT_QSPI_CFG_WP_CLR_MSK    0xffffbfff
/* The reset value of the ALT_QSPI_CFG_WP register field. */
#define ALT_QSPI_CFG_WP_RESET      0x0
/* Extracts the ALT_QSPI_CFG_WP field value from a register. */
#define ALT_QSPI_CFG_WP_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_QSPI_CFG_WP register field value suitable for setting the register. */
#define ALT_QSPI_CFG_WP_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : Enable DMA Peripheral Interface - endma
 * 
 * Allows DMA handshaking mode. When enabled the QSPI will trigger DMA transfer
 * requests via the DMA peripheral interface.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                     | Value | Description     
 * :-------------------------|:------|:-----------------
 *  ALT_QSPI_CFG_ENDMA_E_EN  | 0x1   | Enable DMA Mode 
 *  ALT_QSPI_CFG_ENDMA_E_DIS | 0x0   | Disable DMA Mode
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_CFG_ENDMA
 * 
 * Enable DMA Mode
 */
#define ALT_QSPI_CFG_ENDMA_E_EN     0x1
/*
 * Enumerated value for register field ALT_QSPI_CFG_ENDMA
 * 
 * Disable DMA Mode
 */
#define ALT_QSPI_CFG_ENDMA_E_DIS    0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_CFG_ENDMA register field. */
#define ALT_QSPI_CFG_ENDMA_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_QSPI_CFG_ENDMA register field. */
#define ALT_QSPI_CFG_ENDMA_MSB        15
/* The width in bits of the ALT_QSPI_CFG_ENDMA register field. */
#define ALT_QSPI_CFG_ENDMA_WIDTH      1
/* The mask used to set the ALT_QSPI_CFG_ENDMA register field value. */
#define ALT_QSPI_CFG_ENDMA_SET_MSK    0x00008000
/* The mask used to clear the ALT_QSPI_CFG_ENDMA register field value. */
#define ALT_QSPI_CFG_ENDMA_CLR_MSK    0xffff7fff
/* The reset value of the ALT_QSPI_CFG_ENDMA register field. */
#define ALT_QSPI_CFG_ENDMA_RESET      0x0
/* Extracts the ALT_QSPI_CFG_ENDMA field value from a register. */
#define ALT_QSPI_CFG_ENDMA_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_QSPI_CFG_ENDMA register field value suitable for setting the register. */
#define ALT_QSPI_CFG_ENDMA_SET(value) (((value) << 15) & 0x00008000)

/*
 * Field : Enable AHB Address Re-mapping - enahbremap
 * 
 * (Direct Access Mode Only) When enabled, the incoming AHB address will be adapted
 * and sent to the FLASH device as (address + N), where N is the value stored in
 * the remap address register.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description           
 * :------------------------------|:------|:-----------------------
 *  ALT_QSPI_CFG_ENAHBREMAP_E_EN  | 0x1   | Enable AHB Re-mapping 
 *  ALT_QSPI_CFG_ENAHBREMAP_E_DIS | 0x0   | Disable AHB Re-mapping
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_CFG_ENAHBREMAP
 * 
 * Enable AHB Re-mapping
 */
#define ALT_QSPI_CFG_ENAHBREMAP_E_EN    0x1
/*
 * Enumerated value for register field ALT_QSPI_CFG_ENAHBREMAP
 * 
 * Disable AHB Re-mapping
 */
#define ALT_QSPI_CFG_ENAHBREMAP_E_DIS   0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_CFG_ENAHBREMAP register field. */
#define ALT_QSPI_CFG_ENAHBREMAP_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_QSPI_CFG_ENAHBREMAP register field. */
#define ALT_QSPI_CFG_ENAHBREMAP_MSB        16
/* The width in bits of the ALT_QSPI_CFG_ENAHBREMAP register field. */
#define ALT_QSPI_CFG_ENAHBREMAP_WIDTH      1
/* The mask used to set the ALT_QSPI_CFG_ENAHBREMAP register field value. */
#define ALT_QSPI_CFG_ENAHBREMAP_SET_MSK    0x00010000
/* The mask used to clear the ALT_QSPI_CFG_ENAHBREMAP register field value. */
#define ALT_QSPI_CFG_ENAHBREMAP_CLR_MSK    0xfffeffff
/* The reset value of the ALT_QSPI_CFG_ENAHBREMAP register field. */
#define ALT_QSPI_CFG_ENAHBREMAP_RESET      0x0
/* Extracts the ALT_QSPI_CFG_ENAHBREMAP field value from a register. */
#define ALT_QSPI_CFG_ENAHBREMAP_GET(value) (((value) & 0x00010000) >> 16)
/* Produces a ALT_QSPI_CFG_ENAHBREMAP register field value suitable for setting the register. */
#define ALT_QSPI_CFG_ENAHBREMAP_SET(value) (((value) << 16) & 0x00010000)

/*
 * Field : Enter XIP Mode on next READ - enterxipnextrd
 * 
 * If XIP is enabled, then setting to disabled will cause the controller to exit
 * XIP mode on the next READ instruction. If XIP is disabled, then setting to
 * enabled will inform the controller that the device is ready to enter XIP on the
 * next READ instruction. The controller will therefore send the appropriate
 * command sequence, including mode bits to cause the device to enter XIP mode. Use
 * this register after the controller has ensured the FLASH device has been
 * configured to be ready to enter XIP mode. Note : To exit XIP mode, this bit
 * should be set to 0. This will take effect in the attached device only AFTER the
 * next READ instruction is executed. Software should therefore ensure that at
 * least one READ instruction is requested after resetting this bit before it can
 * be sure XIP mode in the device is exited.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                            
 * :----------------------------------|:------|:----------------------------------------
 *  ALT_QSPI_CFG_ENTERXIPNEXTRD_E_EN  | 0x1   | Enter XIP Mode on next READ instruction
 *  ALT_QSPI_CFG_ENTERXIPNEXTRD_E_DIS | 0x0   | Exit XIP Mode on next READ instruction 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_CFG_ENTERXIPNEXTRD
 * 
 * Enter XIP Mode on next READ instruction
 */
#define ALT_QSPI_CFG_ENTERXIPNEXTRD_E_EN    0x1
/*
 * Enumerated value for register field ALT_QSPI_CFG_ENTERXIPNEXTRD
 * 
 * Exit XIP Mode on next READ instruction
 */
#define ALT_QSPI_CFG_ENTERXIPNEXTRD_E_DIS   0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_CFG_ENTERXIPNEXTRD register field. */
#define ALT_QSPI_CFG_ENTERXIPNEXTRD_LSB        17
/* The Most Significant Bit (MSB) position of the ALT_QSPI_CFG_ENTERXIPNEXTRD register field. */
#define ALT_QSPI_CFG_ENTERXIPNEXTRD_MSB        17
/* The width in bits of the ALT_QSPI_CFG_ENTERXIPNEXTRD register field. */
#define ALT_QSPI_CFG_ENTERXIPNEXTRD_WIDTH      1
/* The mask used to set the ALT_QSPI_CFG_ENTERXIPNEXTRD register field value. */
#define ALT_QSPI_CFG_ENTERXIPNEXTRD_SET_MSK    0x00020000
/* The mask used to clear the ALT_QSPI_CFG_ENTERXIPNEXTRD register field value. */
#define ALT_QSPI_CFG_ENTERXIPNEXTRD_CLR_MSK    0xfffdffff
/* The reset value of the ALT_QSPI_CFG_ENTERXIPNEXTRD register field. */
#define ALT_QSPI_CFG_ENTERXIPNEXTRD_RESET      0x0
/* Extracts the ALT_QSPI_CFG_ENTERXIPNEXTRD field value from a register. */
#define ALT_QSPI_CFG_ENTERXIPNEXTRD_GET(value) (((value) & 0x00020000) >> 17)
/* Produces a ALT_QSPI_CFG_ENTERXIPNEXTRD register field value suitable for setting the register. */
#define ALT_QSPI_CFG_ENTERXIPNEXTRD_SET(value) (((value) << 17) & 0x00020000)

/*
 * Field : Enter XIP Mode Immediately - enterxipimm
 * 
 * If XIP is enabled, then setting to disabled will cause the controller to exit
 * XIP mode on the next READ instruction. If XIP is disabled, then setting enable
 * will operate the device in XIP mode immediately. Use this register when the
 * external device wakes up in XIP mode (as per the contents of its non- volatile
 * configuration register). The controller will assume the next READ instruction
 * will be passed to the device as an XIP instruction, and therefore will not
 * require the READ opcode to be transferred. Note: To exit XIP mode, this bit
 * should be set to 0. This will take effect in the attached device only after the
 * next READ instruction is executed. Software therefore should ensure that at
 * least one READ instruction is requested after resetting this bit in order to be
 * sure that XIP mode is exited.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description                           
 * :-------------------------------|:------|:---------------------------------------
 *  ALT_QSPI_CFG_ENTERXIPIMM_E_EN  | 0x1   | Enter XIP Mode immediately            
 *  ALT_QSPI_CFG_ENTERXIPIMM_E_DIS | 0x0   | Exit XIP Mode on next READ instruction
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_CFG_ENTERXIPIMM
 * 
 * Enter XIP Mode immediately
 */
#define ALT_QSPI_CFG_ENTERXIPIMM_E_EN   0x1
/*
 * Enumerated value for register field ALT_QSPI_CFG_ENTERXIPIMM
 * 
 * Exit XIP Mode on next READ instruction
 */
#define ALT_QSPI_CFG_ENTERXIPIMM_E_DIS  0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_CFG_ENTERXIPIMM register field. */
#define ALT_QSPI_CFG_ENTERXIPIMM_LSB        18
/* The Most Significant Bit (MSB) position of the ALT_QSPI_CFG_ENTERXIPIMM register field. */
#define ALT_QSPI_CFG_ENTERXIPIMM_MSB        18
/* The width in bits of the ALT_QSPI_CFG_ENTERXIPIMM register field. */
#define ALT_QSPI_CFG_ENTERXIPIMM_WIDTH      1
/* The mask used to set the ALT_QSPI_CFG_ENTERXIPIMM register field value. */
#define ALT_QSPI_CFG_ENTERXIPIMM_SET_MSK    0x00040000
/* The mask used to clear the ALT_QSPI_CFG_ENTERXIPIMM register field value. */
#define ALT_QSPI_CFG_ENTERXIPIMM_CLR_MSK    0xfffbffff
/* The reset value of the ALT_QSPI_CFG_ENTERXIPIMM register field. */
#define ALT_QSPI_CFG_ENTERXIPIMM_RESET      0x0
/* Extracts the ALT_QSPI_CFG_ENTERXIPIMM field value from a register. */
#define ALT_QSPI_CFG_ENTERXIPIMM_GET(value) (((value) & 0x00040000) >> 18)
/* Produces a ALT_QSPI_CFG_ENTERXIPIMM register field value suitable for setting the register. */
#define ALT_QSPI_CFG_ENTERXIPIMM_SET(value) (((value) << 18) & 0x00040000)

/*
 * Field : Master Mode Baud Rate Divisor - bauddiv
 * 
 * SPI baud rate = ref_clk / (2 * baud_rate_divisor)
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description     
 * :------------------------------|:------|:-----------------
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD2  | 0x0   | Baud Rate Div/2 
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD4  | 0x1   | Baud Rate Div/4 
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD6  | 0x2   | Baud Rate Div/6 
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD8  | 0x3   | Baud Rate Div/8 
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD10 | 0x4   | Baud Rate Div/10
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD12 | 0x5   | Baud Rate Div/12
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD14 | 0x6   | Baud Rate Div/14
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD16 | 0x7   | Baud Rate Div/16
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD18 | 0x8   | Baud Rate Div/18
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD20 | 0x9   | Baud Rate Div/20
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD22 | 0xa   | Baud Rate Div/22
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD24 | 0xb   | Baud Rate Div/24
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD26 | 0xc   | Baud Rate Div/26
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD28 | 0xd   | Baud Rate Div/28
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD30 | 0xe   | Baud Rate Div/30
 *  ALT_QSPI_CFG_BAUDDIV_E_BAUD32 | 0xf   | Baud Rate Div/32
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/2
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD2    0x0
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/4
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD4    0x1
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/6
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD6    0x2
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/8
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD8    0x3
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/10
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD10   0x4
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/12
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD12   0x5
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/14
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD14   0x6
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/16
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD16   0x7
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/18
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD18   0x8
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/20
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD20   0x9
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/22
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD22   0xa
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/24
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD24   0xb
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/26
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD26   0xc
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/28
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD28   0xd
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/30
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD30   0xe
/*
 * Enumerated value for register field ALT_QSPI_CFG_BAUDDIV
 * 
 * Baud Rate Div/32
 */
#define ALT_QSPI_CFG_BAUDDIV_E_BAUD32   0xf

/* The Least Significant Bit (LSB) position of the ALT_QSPI_CFG_BAUDDIV register field. */
#define ALT_QSPI_CFG_BAUDDIV_LSB        19
/* The Most Significant Bit (MSB) position of the ALT_QSPI_CFG_BAUDDIV register field. */
#define ALT_QSPI_CFG_BAUDDIV_MSB        22
/* The width in bits of the ALT_QSPI_CFG_BAUDDIV register field. */
#define ALT_QSPI_CFG_BAUDDIV_WIDTH      4
/* The mask used to set the ALT_QSPI_CFG_BAUDDIV register field value. */
#define ALT_QSPI_CFG_BAUDDIV_SET_MSK    0x00780000
/* The mask used to clear the ALT_QSPI_CFG_BAUDDIV register field value. */
#define ALT_QSPI_CFG_BAUDDIV_CLR_MSK    0xff87ffff
/* The reset value of the ALT_QSPI_CFG_BAUDDIV register field. */
#define ALT_QSPI_CFG_BAUDDIV_RESET      0xf
/* Extracts the ALT_QSPI_CFG_BAUDDIV field value from a register. */
#define ALT_QSPI_CFG_BAUDDIV_GET(value) (((value) & 0x00780000) >> 19)
/* Produces a ALT_QSPI_CFG_BAUDDIV register field value suitable for setting the register. */
#define ALT_QSPI_CFG_BAUDDIV_SET(value) (((value) << 19) & 0x00780000)

/*
 * Field : Serial interface and QSPI pipeline is IDLE - idle
 * 
 * This is a STATUS read-only bit. Note this is a retimed signal, so there will be
 * some inherent delay on the generation of this status signal.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description  
 * :---------------------------|:------|:--------------
 *  ALT_QSPI_CFG_IDLE_E_SET    | 0x1   | Idle Mode    
 *  ALT_QSPI_CFG_IDLE_E_NOTSET | 0x0   | Non-Idle Mode
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_CFG_IDLE
 * 
 * Idle Mode
 */
#define ALT_QSPI_CFG_IDLE_E_SET     0x1
/*
 * Enumerated value for register field ALT_QSPI_CFG_IDLE
 * 
 * Non-Idle Mode
 */
#define ALT_QSPI_CFG_IDLE_E_NOTSET  0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_CFG_IDLE register field. */
#define ALT_QSPI_CFG_IDLE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_QSPI_CFG_IDLE register field. */
#define ALT_QSPI_CFG_IDLE_MSB        31
/* The width in bits of the ALT_QSPI_CFG_IDLE register field. */
#define ALT_QSPI_CFG_IDLE_WIDTH      1
/* The mask used to set the ALT_QSPI_CFG_IDLE register field value. */
#define ALT_QSPI_CFG_IDLE_SET_MSK    0x80000000
/* The mask used to clear the ALT_QSPI_CFG_IDLE register field value. */
#define ALT_QSPI_CFG_IDLE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_QSPI_CFG_IDLE register field. */
#define ALT_QSPI_CFG_IDLE_RESET      0x0
/* Extracts the ALT_QSPI_CFG_IDLE field value from a register. */
#define ALT_QSPI_CFG_IDLE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_QSPI_CFG_IDLE register field value suitable for setting the register. */
#define ALT_QSPI_CFG_IDLE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_CFG.
 */
struct ALT_QSPI_CFG_s
{
    uint32_t        en             :  1;  /* QSPI Enable */
    uint32_t        selclkpol      :  1;  /* Clock Polarity */
    uint32_t        selclkphase    :  1;  /* Select Clock Phase */
    uint32_t                       :  4;  /* *UNDEFINED* */
    uint32_t        endiracc       :  1;  /* Enable Direct Access Controller */
    uint32_t        enlegacyip     :  1;  /* Legacy IP Mode Enable */
    uint32_t        perseldec      :  1;  /* Peripheral select decode */
    uint32_t        percslines     :  4;  /* Peripheral Chip Select Lines */
    uint32_t        wp             :  1;  /* Write Protect Flash Pin */
    uint32_t        endma          :  1;  /* Enable DMA Peripheral Interface */
    uint32_t        enahbremap     :  1;  /* Enable AHB Address Re-mapping */
    uint32_t        enterxipnextrd :  1;  /* Enter XIP Mode on next READ */
    uint32_t        enterxipimm    :  1;  /* Enter XIP Mode Immediately */
    uint32_t        bauddiv        :  4;  /* Master Mode Baud Rate Divisor */
    uint32_t                       :  8;  /* *UNDEFINED* */
    const uint32_t  idle           :  1;  /* Serial interface and QSPI pipeline is IDLE */
};

/* The typedef declaration for register ALT_QSPI_CFG. */
typedef volatile struct ALT_QSPI_CFG_s  ALT_QSPI_CFG_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_CFG register from the beginning of the component. */
#define ALT_QSPI_CFG_OFST        0x0

/*
 * Register : Device Read Instruction Register - devrd
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                
 * :--------|:-------|:------|:----------------------------
 *  [7:0]   | RW     | 0x3   | Read Opcode in non-XIP mode
 *  [9:8]   | RW     | 0x0   | Instruction Transfer Width 
 *  [11:10] | ???    | 0x0   | *UNDEFINED*                
 *  [13:12] | RW     | 0x0   | Address Transfer Width     
 *  [15:14] | ???    | 0x0   | *UNDEFINED*                
 *  [17:16] | RW     | 0x0   | Data Transfer Width        
 *  [19:18] | ???    | 0x0   | *UNDEFINED*                
 *  [20]    | RW     | 0x0   | Mode Bit Enable            
 *  [23:21] | ???    | 0x0   | *UNDEFINED*                
 *  [28:24] | RW     | 0x0   | Dummy Read Clock Cycles    
 *  [31:29] | ???    | 0x0   | *UNDEFINED*                
 * 
 */
/*
 * Field : Read Opcode in non-XIP mode - rdopcode
 * 
 * Read Opcode to use when not in XIP mode
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                
 * :---------------------------------|:------|:----------------------------
 *  ALT_QSPI_DEVRD_RDOPCODE_E_RD     | 0x3   | Read Opcode in Non-XIP mode
 *  ALT_QSPI_DEVRD_RDOPCODE_E_FASTRD | 0xb   | Fast Read in Non-XIP mode  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_DEVRD_RDOPCODE
 * 
 * Read Opcode in Non-XIP mode
 */
#define ALT_QSPI_DEVRD_RDOPCODE_E_RD        0x3
/*
 * Enumerated value for register field ALT_QSPI_DEVRD_RDOPCODE
 * 
 * Fast Read in Non-XIP mode
 */
#define ALT_QSPI_DEVRD_RDOPCODE_E_FASTRD    0xb

/* The Least Significant Bit (LSB) position of the ALT_QSPI_DEVRD_RDOPCODE register field. */
#define ALT_QSPI_DEVRD_RDOPCODE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DEVRD_RDOPCODE register field. */
#define ALT_QSPI_DEVRD_RDOPCODE_MSB        7
/* The width in bits of the ALT_QSPI_DEVRD_RDOPCODE register field. */
#define ALT_QSPI_DEVRD_RDOPCODE_WIDTH      8
/* The mask used to set the ALT_QSPI_DEVRD_RDOPCODE register field value. */
#define ALT_QSPI_DEVRD_RDOPCODE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_QSPI_DEVRD_RDOPCODE register field value. */
#define ALT_QSPI_DEVRD_RDOPCODE_CLR_MSK    0xffffff00
/* The reset value of the ALT_QSPI_DEVRD_RDOPCODE register field. */
#define ALT_QSPI_DEVRD_RDOPCODE_RESET      0x3
/* Extracts the ALT_QSPI_DEVRD_RDOPCODE field value from a register. */
#define ALT_QSPI_DEVRD_RDOPCODE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_QSPI_DEVRD_RDOPCODE register field value suitable for setting the register. */
#define ALT_QSPI_DEVRD_RDOPCODE_SET(value) (((value) << 0) & 0x000000ff)

/*
 * Field : Instruction Transfer Width - instwidth
 * 
 * Sets instruction transfer width (1, 2, or 4 bits). Applies to all instructions
 * sent to SPI flash device (not just read instructions).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                     
 * :----------------------------------|:------|:-------------------------------------------------
 *  ALT_QSPI_DEVRD_INSTWIDTH_E_SINGLE | 0x0   | Instruction transferred on DQ0. Supported by all
 * :                                  |       | SPI flash devices.                              
 *  ALT_QSPI_DEVRD_INSTWIDTH_E_DUAL   | 0x1   | Instruction transferred on DQ0 and DQ1.         
 * :                                  |       | Supported by all SPI flash devices that support 
 * :                                  |       | the Dual SP (DIO-SPI) Protocol.                 
 *  ALT_QSPI_DEVRD_INSTWIDTH_E_QUAD   | 0x2   | Instruction transferred on DQ0, DQ1, DQ2, and   
 * :                                  |       | DQ3. Supported by all SPI flash devices that    
 * :                                  |       | support the Quad SP (QIO-SPI) Protocol.         
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_DEVRD_INSTWIDTH
 * 
 * Instruction transferred on DQ0. Supported by all SPI flash devices.
 */
#define ALT_QSPI_DEVRD_INSTWIDTH_E_SINGLE   0x0
/*
 * Enumerated value for register field ALT_QSPI_DEVRD_INSTWIDTH
 * 
 * Instruction transferred on DQ0 and DQ1. Supported by all SPI flash devices that
 * support the Dual SP (DIO-SPI) Protocol.
 */
#define ALT_QSPI_DEVRD_INSTWIDTH_E_DUAL     0x1
/*
 * Enumerated value for register field ALT_QSPI_DEVRD_INSTWIDTH
 * 
 * Instruction transferred on DQ0, DQ1, DQ2, and DQ3. Supported by all SPI flash
 * devices that support the Quad SP (QIO-SPI) Protocol.
 */
#define ALT_QSPI_DEVRD_INSTWIDTH_E_QUAD     0x2

/* The Least Significant Bit (LSB) position of the ALT_QSPI_DEVRD_INSTWIDTH register field. */
#define ALT_QSPI_DEVRD_INSTWIDTH_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DEVRD_INSTWIDTH register field. */
#define ALT_QSPI_DEVRD_INSTWIDTH_MSB        9
/* The width in bits of the ALT_QSPI_DEVRD_INSTWIDTH register field. */
#define ALT_QSPI_DEVRD_INSTWIDTH_WIDTH      2
/* The mask used to set the ALT_QSPI_DEVRD_INSTWIDTH register field value. */
#define ALT_QSPI_DEVRD_INSTWIDTH_SET_MSK    0x00000300
/* The mask used to clear the ALT_QSPI_DEVRD_INSTWIDTH register field value. */
#define ALT_QSPI_DEVRD_INSTWIDTH_CLR_MSK    0xfffffcff
/* The reset value of the ALT_QSPI_DEVRD_INSTWIDTH register field. */
#define ALT_QSPI_DEVRD_INSTWIDTH_RESET      0x0
/* Extracts the ALT_QSPI_DEVRD_INSTWIDTH field value from a register. */
#define ALT_QSPI_DEVRD_INSTWIDTH_GET(value) (((value) & 0x00000300) >> 8)
/* Produces a ALT_QSPI_DEVRD_INSTWIDTH register field value suitable for setting the register. */
#define ALT_QSPI_DEVRD_INSTWIDTH_SET(value) (((value) << 8) & 0x00000300)

/*
 * Field : Address Transfer Width - addrwidth
 * 
 * Sets read address transfer width (1, 2, or 4 bits).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                     
 * :----------------------------------|:------|:-------------------------------------------------
 *  ALT_QSPI_DEVRD_ADDRWIDTH_E_SINGLE | 0x0   | Read address transferred on DQ0. Supported by   
 * :                                  |       | all SPI flash devices                           
 *  ALT_QSPI_DEVRD_ADDRWIDTH_E_DUAL   | 0x1   | Read address transferred on DQ0 and DQ1.        
 * :                                  |       | Supported by some SPI flash devices that support
 * :                                  |       | the Extended SPI Protocol and by all SPI flash  
 * :                                  |       | devices that support the Dual SP (DIO-SPI)      
 * :                                  |       | Protocol.                                       
 *  ALT_QSPI_DEVRD_ADDRWIDTH_E_QUAD   | 0x2   | Read address transferred on DQ0, DQ1, DQ2, and  
 * :                                  |       | DQ3. Supported by some SPI flash devices that   
 * :                                  |       | support the Extended SPI Protocol and by all SPI
 * :                                  |       | flash devices that support the Quad SP (QIO-SPI)
 * :                                  |       | Protocol.                                       
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_DEVRD_ADDRWIDTH
 * 
 * Read address transferred on DQ0. Supported by all SPI flash devices
 */
#define ALT_QSPI_DEVRD_ADDRWIDTH_E_SINGLE   0x0
/*
 * Enumerated value for register field ALT_QSPI_DEVRD_ADDRWIDTH
 * 
 * Read address transferred on DQ0 and DQ1. Supported by some SPI flash devices
 * that support the Extended SPI Protocol and by all SPI flash devices that support
 * the Dual SP (DIO-SPI) Protocol.
 */
#define ALT_QSPI_DEVRD_ADDRWIDTH_E_DUAL     0x1
/*
 * Enumerated value for register field ALT_QSPI_DEVRD_ADDRWIDTH
 * 
 * Read address transferred on DQ0, DQ1, DQ2, and DQ3. Supported by some SPI flash
 * devices that support the Extended SPI Protocol and by all SPI flash devices that
 * support the Quad SP (QIO-SPI) Protocol.
 */
#define ALT_QSPI_DEVRD_ADDRWIDTH_E_QUAD     0x2

/* The Least Significant Bit (LSB) position of the ALT_QSPI_DEVRD_ADDRWIDTH register field. */
#define ALT_QSPI_DEVRD_ADDRWIDTH_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DEVRD_ADDRWIDTH register field. */
#define ALT_QSPI_DEVRD_ADDRWIDTH_MSB        13
/* The width in bits of the ALT_QSPI_DEVRD_ADDRWIDTH register field. */
#define ALT_QSPI_DEVRD_ADDRWIDTH_WIDTH      2
/* The mask used to set the ALT_QSPI_DEVRD_ADDRWIDTH register field value. */
#define ALT_QSPI_DEVRD_ADDRWIDTH_SET_MSK    0x00003000
/* The mask used to clear the ALT_QSPI_DEVRD_ADDRWIDTH register field value. */
#define ALT_QSPI_DEVRD_ADDRWIDTH_CLR_MSK    0xffffcfff
/* The reset value of the ALT_QSPI_DEVRD_ADDRWIDTH register field. */
#define ALT_QSPI_DEVRD_ADDRWIDTH_RESET      0x0
/* Extracts the ALT_QSPI_DEVRD_ADDRWIDTH field value from a register. */
#define ALT_QSPI_DEVRD_ADDRWIDTH_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_QSPI_DEVRD_ADDRWIDTH register field value suitable for setting the register. */
#define ALT_QSPI_DEVRD_ADDRWIDTH_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Data Transfer Width - datawidth
 * 
 * Sets read data transfer width (1, 2, or 4 bits).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                     
 * :----------------------------------|:------|:-------------------------------------------------
 *  ALT_QSPI_DEVRD_DATAWIDTH_E_SINGLE | 0x0   | Read data transferred on DQ0. Supported by all  
 * :                                  |       | SPI flash devices                               
 *  ALT_QSPI_DEVRD_DATAWIDTH_E_DUAL   | 0x1   | Read data transferred on DQ0 and DQ1. Supported 
 * :                                  |       | by some SPI flash devices that support the      
 * :                                  |       | Extended SPI Protocol and by all SPI flash      
 * :                                  |       | devices that support the Dual SP (DIO-SPI)      
 * :                                  |       | Protocol.                                       
 *  ALT_QSPI_DEVRD_DATAWIDTH_E_QUAD   | 0x2   | Read data transferred on DQ0, DQ1, DQ2, and DQ3.
 * :                                  |       | Supported by some SPI flash devices that support
 * :                                  |       | the Extended SPI Protocol and by all SPI flash  
 * :                                  |       | devices that support the Quad SP (QIO-SPI)      
 * :                                  |       | Protocol.                                       
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_DEVRD_DATAWIDTH
 * 
 * Read data transferred on DQ0. Supported by all SPI flash devices
 */
#define ALT_QSPI_DEVRD_DATAWIDTH_E_SINGLE   0x0
/*
 * Enumerated value for register field ALT_QSPI_DEVRD_DATAWIDTH
 * 
 * Read data transferred on DQ0 and DQ1. Supported by some SPI flash devices that
 * support the Extended SPI Protocol and by all SPI flash devices that support the
 * Dual SP (DIO-SPI) Protocol.
 */
#define ALT_QSPI_DEVRD_DATAWIDTH_E_DUAL     0x1
/*
 * Enumerated value for register field ALT_QSPI_DEVRD_DATAWIDTH
 * 
 * Read data transferred on DQ0, DQ1, DQ2, and DQ3. Supported by some SPI flash
 * devices that support the Extended SPI Protocol and by all SPI flash devices that
 * support the Quad SP (QIO-SPI) Protocol.
 */
#define ALT_QSPI_DEVRD_DATAWIDTH_E_QUAD     0x2

/* The Least Significant Bit (LSB) position of the ALT_QSPI_DEVRD_DATAWIDTH register field. */
#define ALT_QSPI_DEVRD_DATAWIDTH_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DEVRD_DATAWIDTH register field. */
#define ALT_QSPI_DEVRD_DATAWIDTH_MSB        17
/* The width in bits of the ALT_QSPI_DEVRD_DATAWIDTH register field. */
#define ALT_QSPI_DEVRD_DATAWIDTH_WIDTH      2
/* The mask used to set the ALT_QSPI_DEVRD_DATAWIDTH register field value. */
#define ALT_QSPI_DEVRD_DATAWIDTH_SET_MSK    0x00030000
/* The mask used to clear the ALT_QSPI_DEVRD_DATAWIDTH register field value. */
#define ALT_QSPI_DEVRD_DATAWIDTH_CLR_MSK    0xfffcffff
/* The reset value of the ALT_QSPI_DEVRD_DATAWIDTH register field. */
#define ALT_QSPI_DEVRD_DATAWIDTH_RESET      0x0
/* Extracts the ALT_QSPI_DEVRD_DATAWIDTH field value from a register. */
#define ALT_QSPI_DEVRD_DATAWIDTH_GET(value) (((value) & 0x00030000) >> 16)
/* Produces a ALT_QSPI_DEVRD_DATAWIDTH register field value suitable for setting the register. */
#define ALT_QSPI_DEVRD_DATAWIDTH_SET(value) (((value) << 16) & 0x00030000)

/*
 * Field : Mode Bit Enable - enmodebits
 * 
 * If this bit is set, the mode bits as defined in the Mode Bit Configuration
 * register are sent following the address bytes.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                   
 * :-----------------------------------|:------|:-------------------------------
 *  ALT_QSPI_DEVRD_ENMODBITS_E_NOORDER | 0x0   | No Order                      
 *  ALT_QSPI_DEVRD_ENMODBITS_E_ORDER   | 0x1   | Mode Bits follow address bytes
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_DEVRD_ENMODBITS
 * 
 * No Order
 */
#define ALT_QSPI_DEVRD_ENMODBITS_E_NOORDER  0x0
/*
 * Enumerated value for register field ALT_QSPI_DEVRD_ENMODBITS
 * 
 * Mode Bits follow address bytes
 */
#define ALT_QSPI_DEVRD_ENMODBITS_E_ORDER    0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_DEVRD_ENMODBITS register field. */
#define ALT_QSPI_DEVRD_ENMODBITS_LSB        20
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DEVRD_ENMODBITS register field. */
#define ALT_QSPI_DEVRD_ENMODBITS_MSB        20
/* The width in bits of the ALT_QSPI_DEVRD_ENMODBITS register field. */
#define ALT_QSPI_DEVRD_ENMODBITS_WIDTH      1
/* The mask used to set the ALT_QSPI_DEVRD_ENMODBITS register field value. */
#define ALT_QSPI_DEVRD_ENMODBITS_SET_MSK    0x00100000
/* The mask used to clear the ALT_QSPI_DEVRD_ENMODBITS register field value. */
#define ALT_QSPI_DEVRD_ENMODBITS_CLR_MSK    0xffefffff
/* The reset value of the ALT_QSPI_DEVRD_ENMODBITS register field. */
#define ALT_QSPI_DEVRD_ENMODBITS_RESET      0x0
/* Extracts the ALT_QSPI_DEVRD_ENMODBITS field value from a register. */
#define ALT_QSPI_DEVRD_ENMODBITS_GET(value) (((value) & 0x00100000) >> 20)
/* Produces a ALT_QSPI_DEVRD_ENMODBITS register field value suitable for setting the register. */
#define ALT_QSPI_DEVRD_ENMODBITS_SET(value) (((value) << 20) & 0x00100000)

/*
 * Field : Dummy Read Clock Cycles - dummyrdclks
 * 
 * Number of dummy clock cycles required by device for read instruction.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_DEVRD_DUMMYRDCLKS register field. */
#define ALT_QSPI_DEVRD_DUMMYRDCLKS_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DEVRD_DUMMYRDCLKS register field. */
#define ALT_QSPI_DEVRD_DUMMYRDCLKS_MSB        28
/* The width in bits of the ALT_QSPI_DEVRD_DUMMYRDCLKS register field. */
#define ALT_QSPI_DEVRD_DUMMYRDCLKS_WIDTH      5
/* The mask used to set the ALT_QSPI_DEVRD_DUMMYRDCLKS register field value. */
#define ALT_QSPI_DEVRD_DUMMYRDCLKS_SET_MSK    0x1f000000
/* The mask used to clear the ALT_QSPI_DEVRD_DUMMYRDCLKS register field value. */
#define ALT_QSPI_DEVRD_DUMMYRDCLKS_CLR_MSK    0xe0ffffff
/* The reset value of the ALT_QSPI_DEVRD_DUMMYRDCLKS register field. */
#define ALT_QSPI_DEVRD_DUMMYRDCLKS_RESET      0x0
/* Extracts the ALT_QSPI_DEVRD_DUMMYRDCLKS field value from a register. */
#define ALT_QSPI_DEVRD_DUMMYRDCLKS_GET(value) (((value) & 0x1f000000) >> 24)
/* Produces a ALT_QSPI_DEVRD_DUMMYRDCLKS register field value suitable for setting the register. */
#define ALT_QSPI_DEVRD_DUMMYRDCLKS_SET(value) (((value) << 24) & 0x1f000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_DEVRD.
 */
struct ALT_QSPI_DEVRD_s
{
    uint32_t  rdopcode    :  8;  /* Read Opcode in non-XIP mode */
    uint32_t  instwidth   :  2;  /* Instruction Transfer Width */
    uint32_t              :  2;  /* *UNDEFINED* */
    uint32_t  addrwidth   :  2;  /* Address Transfer Width */
    uint32_t              :  2;  /* *UNDEFINED* */
    uint32_t  datawidth   :  2;  /* Data Transfer Width */
    uint32_t              :  2;  /* *UNDEFINED* */
    uint32_t  enmodebits  :  1;  /* Mode Bit Enable */
    uint32_t              :  3;  /* *UNDEFINED* */
    uint32_t  dummyrdclks :  5;  /* Dummy Read Clock Cycles */
    uint32_t              :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_DEVRD. */
typedef volatile struct ALT_QSPI_DEVRD_s  ALT_QSPI_DEVRD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_DEVRD register from the beginning of the component. */
#define ALT_QSPI_DEVRD_OFST        0x4

/*
 * Register : Device Write Instruction Register - devwr
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description             
 * :--------|:-------|:------|:-------------------------
 *  [7:0]   | RW     | 0x2   | Write Opcode            
 *  [11:8]  | ???    | 0x0   | *UNDEFINED*             
 *  [13:12] | RW     | 0x0   | Address Transfer Width  
 *  [15:14] | ???    | 0x0   | *UNDEFINED*             
 *  [17:16] | RW     | 0x0   | Data Transfer Width     
 *  [23:18] | ???    | 0x0   | *UNDEFINED*             
 *  [28:24] | RW     | 0x0   | Dummy Write Clock Cycles
 *  [31:29] | ???    | 0x0   | *UNDEFINED*             
 * 
 */
/*
 * Field : Write Opcode - wropcode
 * 
 * Write Opcode
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_DEVWR_WROPCODE register field. */
#define ALT_QSPI_DEVWR_WROPCODE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DEVWR_WROPCODE register field. */
#define ALT_QSPI_DEVWR_WROPCODE_MSB        7
/* The width in bits of the ALT_QSPI_DEVWR_WROPCODE register field. */
#define ALT_QSPI_DEVWR_WROPCODE_WIDTH      8
/* The mask used to set the ALT_QSPI_DEVWR_WROPCODE register field value. */
#define ALT_QSPI_DEVWR_WROPCODE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_QSPI_DEVWR_WROPCODE register field value. */
#define ALT_QSPI_DEVWR_WROPCODE_CLR_MSK    0xffffff00
/* The reset value of the ALT_QSPI_DEVWR_WROPCODE register field. */
#define ALT_QSPI_DEVWR_WROPCODE_RESET      0x2
/* Extracts the ALT_QSPI_DEVWR_WROPCODE field value from a register. */
#define ALT_QSPI_DEVWR_WROPCODE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_QSPI_DEVWR_WROPCODE register field value suitable for setting the register. */
#define ALT_QSPI_DEVWR_WROPCODE_SET(value) (((value) << 0) & 0x000000ff)

/*
 * Field : Address Transfer Width - addrwidth
 * 
 * Sets write address transfer width (1, 2, or 4 bits).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                     
 * :----------------------------------|:------|:-------------------------------------------------
 *  ALT_QSPI_DEVWR_ADDRWIDTH_E_SINGLE | 0x0   | Write address transferred on DQ0. Supported by  
 * :                                  |       | all SPI flash devices                           
 *  ALT_QSPI_DEVWR_ADDRWIDTH_E_DUAL   | 0x1   | Read address transferred on DQ0 and DQ1.        
 * :                                  |       | Supported by some SPI flash devices that support
 * :                                  |       | the Extended SPI Protocol and by all SPI flash  
 * :                                  |       | devices that support the Dual SP (DIO-SPI)      
 * :                                  |       | Protocol.                                       
 *  ALT_QSPI_DEVWR_ADDRWIDTH_E_QUAD   | 0x2   | Read address transferred on DQ0, DQ1, DQ2, and  
 * :                                  |       | DQ3. Supported by some SPI flash devices that   
 * :                                  |       | support the Extended SPI Protocol and by all SPI
 * :                                  |       | flash devices that support the Quad SP (QIO-SPI)
 * :                                  |       | Protocol.                                       
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_DEVWR_ADDRWIDTH
 * 
 * Write address transferred on DQ0. Supported by all SPI flash devices
 */
#define ALT_QSPI_DEVWR_ADDRWIDTH_E_SINGLE   0x0
/*
 * Enumerated value for register field ALT_QSPI_DEVWR_ADDRWIDTH
 * 
 * Read address transferred on DQ0 and DQ1. Supported by some SPI flash devices
 * that support the Extended SPI Protocol and by all SPI flash devices that support
 * the Dual SP (DIO-SPI) Protocol.
 */
#define ALT_QSPI_DEVWR_ADDRWIDTH_E_DUAL     0x1
/*
 * Enumerated value for register field ALT_QSPI_DEVWR_ADDRWIDTH
 * 
 * Read address transferred on DQ0, DQ1, DQ2, and DQ3. Supported by some SPI flash
 * devices that support the Extended SPI Protocol and by all SPI flash devices that
 * support the Quad SP (QIO-SPI) Protocol.
 */
#define ALT_QSPI_DEVWR_ADDRWIDTH_E_QUAD     0x2

/* The Least Significant Bit (LSB) position of the ALT_QSPI_DEVWR_ADDRWIDTH register field. */
#define ALT_QSPI_DEVWR_ADDRWIDTH_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DEVWR_ADDRWIDTH register field. */
#define ALT_QSPI_DEVWR_ADDRWIDTH_MSB        13
/* The width in bits of the ALT_QSPI_DEVWR_ADDRWIDTH register field. */
#define ALT_QSPI_DEVWR_ADDRWIDTH_WIDTH      2
/* The mask used to set the ALT_QSPI_DEVWR_ADDRWIDTH register field value. */
#define ALT_QSPI_DEVWR_ADDRWIDTH_SET_MSK    0x00003000
/* The mask used to clear the ALT_QSPI_DEVWR_ADDRWIDTH register field value. */
#define ALT_QSPI_DEVWR_ADDRWIDTH_CLR_MSK    0xffffcfff
/* The reset value of the ALT_QSPI_DEVWR_ADDRWIDTH register field. */
#define ALT_QSPI_DEVWR_ADDRWIDTH_RESET      0x0
/* Extracts the ALT_QSPI_DEVWR_ADDRWIDTH field value from a register. */
#define ALT_QSPI_DEVWR_ADDRWIDTH_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_QSPI_DEVWR_ADDRWIDTH register field value suitable for setting the register. */
#define ALT_QSPI_DEVWR_ADDRWIDTH_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Data Transfer Width - datawidth
 * 
 * Sets write data transfer width (1, 2, or 4 bits).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                     
 * :----------------------------------|:------|:-------------------------------------------------
 *  ALT_QSPI_DEVWR_DATAWIDTH_E_SINGLE | 0x0   | Write data transferred on DQ0. Supported by all 
 * :                                  |       | SPI flash devices                               
 *  ALT_QSPI_DEVWR_DATAWIDTH_E_DUAL   | 0x1   | Read data transferred on DQ0 and DQ1. Supported 
 * :                                  |       | by some SPI flash devices that support the      
 * :                                  |       | Extended SPI Protocol and by all SPI flash      
 * :                                  |       | devices that support the Dual SP (DIO-SPI)      
 * :                                  |       | Protocol.                                       
 *  ALT_QSPI_DEVWR_DATAWIDTH_E_QUAD   | 0x2   | Read data transferred on DQ0, DQ1, DQ2, and DQ3.
 * :                                  |       | Supported by some SPI flash devices that support
 * :                                  |       | the Extended SPI Protocol and by all SPI flash  
 * :                                  |       | devices that support the Quad SP (QIO-SPI)      
 * :                                  |       | Protocol.                                       
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_DEVWR_DATAWIDTH
 * 
 * Write data transferred on DQ0. Supported by all SPI flash devices
 */
#define ALT_QSPI_DEVWR_DATAWIDTH_E_SINGLE   0x0
/*
 * Enumerated value for register field ALT_QSPI_DEVWR_DATAWIDTH
 * 
 * Read data transferred on DQ0 and DQ1. Supported by some SPI flash devices that
 * support the Extended SPI Protocol and by all SPI flash devices that support the
 * Dual SP (DIO-SPI) Protocol.
 */
#define ALT_QSPI_DEVWR_DATAWIDTH_E_DUAL     0x1
/*
 * Enumerated value for register field ALT_QSPI_DEVWR_DATAWIDTH
 * 
 * Read data transferred on DQ0, DQ1, DQ2, and DQ3. Supported by some SPI flash
 * devices that support the Extended SPI Protocol and by all SPI flash devices that
 * support the Quad SP (QIO-SPI) Protocol.
 */
#define ALT_QSPI_DEVWR_DATAWIDTH_E_QUAD     0x2

/* The Least Significant Bit (LSB) position of the ALT_QSPI_DEVWR_DATAWIDTH register field. */
#define ALT_QSPI_DEVWR_DATAWIDTH_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DEVWR_DATAWIDTH register field. */
#define ALT_QSPI_DEVWR_DATAWIDTH_MSB        17
/* The width in bits of the ALT_QSPI_DEVWR_DATAWIDTH register field. */
#define ALT_QSPI_DEVWR_DATAWIDTH_WIDTH      2
/* The mask used to set the ALT_QSPI_DEVWR_DATAWIDTH register field value. */
#define ALT_QSPI_DEVWR_DATAWIDTH_SET_MSK    0x00030000
/* The mask used to clear the ALT_QSPI_DEVWR_DATAWIDTH register field value. */
#define ALT_QSPI_DEVWR_DATAWIDTH_CLR_MSK    0xfffcffff
/* The reset value of the ALT_QSPI_DEVWR_DATAWIDTH register field. */
#define ALT_QSPI_DEVWR_DATAWIDTH_RESET      0x0
/* Extracts the ALT_QSPI_DEVWR_DATAWIDTH field value from a register. */
#define ALT_QSPI_DEVWR_DATAWIDTH_GET(value) (((value) & 0x00030000) >> 16)
/* Produces a ALT_QSPI_DEVWR_DATAWIDTH register field value suitable for setting the register. */
#define ALT_QSPI_DEVWR_DATAWIDTH_SET(value) (((value) << 16) & 0x00030000)

/*
 * Field : Dummy Write Clock Cycles - dummywrclks
 * 
 * Number of dummy clock cycles required by device for write instruction.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_DEVWR_DUMMYWRCLKS register field. */
#define ALT_QSPI_DEVWR_DUMMYWRCLKS_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DEVWR_DUMMYWRCLKS register field. */
#define ALT_QSPI_DEVWR_DUMMYWRCLKS_MSB        28
/* The width in bits of the ALT_QSPI_DEVWR_DUMMYWRCLKS register field. */
#define ALT_QSPI_DEVWR_DUMMYWRCLKS_WIDTH      5
/* The mask used to set the ALT_QSPI_DEVWR_DUMMYWRCLKS register field value. */
#define ALT_QSPI_DEVWR_DUMMYWRCLKS_SET_MSK    0x1f000000
/* The mask used to clear the ALT_QSPI_DEVWR_DUMMYWRCLKS register field value. */
#define ALT_QSPI_DEVWR_DUMMYWRCLKS_CLR_MSK    0xe0ffffff
/* The reset value of the ALT_QSPI_DEVWR_DUMMYWRCLKS register field. */
#define ALT_QSPI_DEVWR_DUMMYWRCLKS_RESET      0x0
/* Extracts the ALT_QSPI_DEVWR_DUMMYWRCLKS field value from a register. */
#define ALT_QSPI_DEVWR_DUMMYWRCLKS_GET(value) (((value) & 0x1f000000) >> 24)
/* Produces a ALT_QSPI_DEVWR_DUMMYWRCLKS register field value suitable for setting the register. */
#define ALT_QSPI_DEVWR_DUMMYWRCLKS_SET(value) (((value) << 24) & 0x1f000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_DEVWR.
 */
struct ALT_QSPI_DEVWR_s
{
    uint32_t  wropcode    :  8;  /* Write Opcode */
    uint32_t              :  4;  /* *UNDEFINED* */
    uint32_t  addrwidth   :  2;  /* Address Transfer Width */
    uint32_t              :  2;  /* *UNDEFINED* */
    uint32_t  datawidth   :  2;  /* Data Transfer Width */
    uint32_t              :  6;  /* *UNDEFINED* */
    uint32_t  dummywrclks :  5;  /* Dummy Write Clock Cycles */
    uint32_t              :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_DEVWR. */
typedef volatile struct ALT_QSPI_DEVWR_s  ALT_QSPI_DEVWR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_DEVWR register from the beginning of the component. */
#define ALT_QSPI_DEVWR_OFST        0x8

/*
 * Register : QSPI Device Delay Register - delay
 * 
 * This register is used to introduce relative delays into the generation of the
 * master output signals. All timings are defined in cycles of the qspi_clk.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                             
 * :--------|:-------|:------|:-----------------------------------------
 *  [7:0]   | RW     | 0x0   | Clock Delay with qspi_n_ss_out          
 *  [15:8]  | RW     | 0x0   | Clock Delay for Last Transaction Bit    
 *  [23:16] | RW     | 0x0   | Clock Delay for Chip Select Deactivation
 *  [31:24] | RW     | 0x0   | Clock Delay for Chip Select Deassert    
 * 
 */
/*
 * Field : Clock Delay with qspi_n_ss_out - init
 * 
 * Delay in master reference clocks between setting qspi_n_ss_out low and first bit
 * transfer.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_DELAY_INIT register field. */
#define ALT_QSPI_DELAY_INIT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DELAY_INIT register field. */
#define ALT_QSPI_DELAY_INIT_MSB        7
/* The width in bits of the ALT_QSPI_DELAY_INIT register field. */
#define ALT_QSPI_DELAY_INIT_WIDTH      8
/* The mask used to set the ALT_QSPI_DELAY_INIT register field value. */
#define ALT_QSPI_DELAY_INIT_SET_MSK    0x000000ff
/* The mask used to clear the ALT_QSPI_DELAY_INIT register field value. */
#define ALT_QSPI_DELAY_INIT_CLR_MSK    0xffffff00
/* The reset value of the ALT_QSPI_DELAY_INIT register field. */
#define ALT_QSPI_DELAY_INIT_RESET      0x0
/* Extracts the ALT_QSPI_DELAY_INIT field value from a register. */
#define ALT_QSPI_DELAY_INIT_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_QSPI_DELAY_INIT register field value suitable for setting the register. */
#define ALT_QSPI_DELAY_INIT_SET(value) (((value) << 0) & 0x000000ff)

/*
 * Field : Clock Delay for Last Transaction Bit - after
 * 
 * Delay in master reference clocks between last bit of current transaction and
 * deasserting the device chip select (qspi_n_ss_out). By default, the chip select
 * will be deasserted on the cycle following the completion of the current
 * transaction.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_DELAY_AFTER register field. */
#define ALT_QSPI_DELAY_AFTER_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DELAY_AFTER register field. */
#define ALT_QSPI_DELAY_AFTER_MSB        15
/* The width in bits of the ALT_QSPI_DELAY_AFTER register field. */
#define ALT_QSPI_DELAY_AFTER_WIDTH      8
/* The mask used to set the ALT_QSPI_DELAY_AFTER register field value. */
#define ALT_QSPI_DELAY_AFTER_SET_MSK    0x0000ff00
/* The mask used to clear the ALT_QSPI_DELAY_AFTER register field value. */
#define ALT_QSPI_DELAY_AFTER_CLR_MSK    0xffff00ff
/* The reset value of the ALT_QSPI_DELAY_AFTER register field. */
#define ALT_QSPI_DELAY_AFTER_RESET      0x0
/* Extracts the ALT_QSPI_DELAY_AFTER field value from a register. */
#define ALT_QSPI_DELAY_AFTER_GET(value) (((value) & 0x0000ff00) >> 8)
/* Produces a ALT_QSPI_DELAY_AFTER register field value suitable for setting the register. */
#define ALT_QSPI_DELAY_AFTER_SET(value) (((value) << 8) & 0x0000ff00)

/*
 * Field : Clock Delay for Chip Select Deactivation - btwn
 * 
 * Delay in master reference clocks between one chip select being de-activated and
 * the activation of another. This is used to ensure a quiet period between the
 * selection of two different slaves and requires the transmit FIFO to be empty.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_DELAY_BTWN register field. */
#define ALT_QSPI_DELAY_BTWN_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DELAY_BTWN register field. */
#define ALT_QSPI_DELAY_BTWN_MSB        23
/* The width in bits of the ALT_QSPI_DELAY_BTWN register field. */
#define ALT_QSPI_DELAY_BTWN_WIDTH      8
/* The mask used to set the ALT_QSPI_DELAY_BTWN register field value. */
#define ALT_QSPI_DELAY_BTWN_SET_MSK    0x00ff0000
/* The mask used to clear the ALT_QSPI_DELAY_BTWN register field value. */
#define ALT_QSPI_DELAY_BTWN_CLR_MSK    0xff00ffff
/* The reset value of the ALT_QSPI_DELAY_BTWN register field. */
#define ALT_QSPI_DELAY_BTWN_RESET      0x0
/* Extracts the ALT_QSPI_DELAY_BTWN field value from a register. */
#define ALT_QSPI_DELAY_BTWN_GET(value) (((value) & 0x00ff0000) >> 16)
/* Produces a ALT_QSPI_DELAY_BTWN register field value suitable for setting the register. */
#define ALT_QSPI_DELAY_BTWN_SET(value) (((value) << 16) & 0x00ff0000)

/*
 * Field : Clock Delay for Chip Select Deassert - nss
 * 
 * Delay in master reference clocks for the length that the master mode chip select
 * outputs are de-asserted between transactions. The minimum delay is always
 * qspi_sck_out period to ensure the chip select is never re-asserted within an
 * qspi_sck_out period.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_DELAY_NSS register field. */
#define ALT_QSPI_DELAY_NSS_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DELAY_NSS register field. */
#define ALT_QSPI_DELAY_NSS_MSB        31
/* The width in bits of the ALT_QSPI_DELAY_NSS register field. */
#define ALT_QSPI_DELAY_NSS_WIDTH      8
/* The mask used to set the ALT_QSPI_DELAY_NSS register field value. */
#define ALT_QSPI_DELAY_NSS_SET_MSK    0xff000000
/* The mask used to clear the ALT_QSPI_DELAY_NSS register field value. */
#define ALT_QSPI_DELAY_NSS_CLR_MSK    0x00ffffff
/* The reset value of the ALT_QSPI_DELAY_NSS register field. */
#define ALT_QSPI_DELAY_NSS_RESET      0x0
/* Extracts the ALT_QSPI_DELAY_NSS field value from a register. */
#define ALT_QSPI_DELAY_NSS_GET(value) (((value) & 0xff000000) >> 24)
/* Produces a ALT_QSPI_DELAY_NSS register field value suitable for setting the register. */
#define ALT_QSPI_DELAY_NSS_SET(value) (((value) << 24) & 0xff000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_DELAY.
 */
struct ALT_QSPI_DELAY_s
{
    uint32_t  init  :  8;  /* Clock Delay with qspi_n_ss_out */
    uint32_t  after :  8;  /* Clock Delay for Last Transaction Bit */
    uint32_t  btwn  :  8;  /* Clock Delay for Chip Select Deactivation */
    uint32_t  nss   :  8;  /* Clock Delay for Chip Select Deassert */
};

/* The typedef declaration for register ALT_QSPI_DELAY. */
typedef volatile struct ALT_QSPI_DELAY_s  ALT_QSPI_DELAY_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_DELAY register from the beginning of the component. */
#define ALT_QSPI_DELAY_OFST        0xc

/*
 * Register : Read Data Capture Register - rddatacap
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [0]    | RW     | 0x1   | Bypass     
 *  [4:1]  | RW     | 0x0   | Read Delay 
 *  [31:5] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Bypass - byp
 * 
 * Controls bypass of the adapted loopback clock circuit
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                  
 * :----------------------------------|:------|:------------------------------
 *  ALT_QSPI_RDDATACAP_BYP_E_NOBYPASS | 0x0   | No Bypass                    
 *  ALT_QSPI_RDDATACAP_BYP_E_BYPASS   | 0x1   | Bypass loopback clock circuit
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_RDDATACAP_BYP
 * 
 * No Bypass
 */
#define ALT_QSPI_RDDATACAP_BYP_E_NOBYPASS   0x0
/*
 * Enumerated value for register field ALT_QSPI_RDDATACAP_BYP
 * 
 * Bypass loopback clock circuit
 */
#define ALT_QSPI_RDDATACAP_BYP_E_BYPASS     0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_RDDATACAP_BYP register field. */
#define ALT_QSPI_RDDATACAP_BYP_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_RDDATACAP_BYP register field. */
#define ALT_QSPI_RDDATACAP_BYP_MSB        0
/* The width in bits of the ALT_QSPI_RDDATACAP_BYP register field. */
#define ALT_QSPI_RDDATACAP_BYP_WIDTH      1
/* The mask used to set the ALT_QSPI_RDDATACAP_BYP register field value. */
#define ALT_QSPI_RDDATACAP_BYP_SET_MSK    0x00000001
/* The mask used to clear the ALT_QSPI_RDDATACAP_BYP register field value. */
#define ALT_QSPI_RDDATACAP_BYP_CLR_MSK    0xfffffffe
/* The reset value of the ALT_QSPI_RDDATACAP_BYP register field. */
#define ALT_QSPI_RDDATACAP_BYP_RESET      0x1
/* Extracts the ALT_QSPI_RDDATACAP_BYP field value from a register. */
#define ALT_QSPI_RDDATACAP_BYP_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_QSPI_RDDATACAP_BYP register field value suitable for setting the register. */
#define ALT_QSPI_RDDATACAP_BYP_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Read Delay - delay
 * 
 * Delay the read data capturing logic by the programmed number of qspi_clk cycles
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_RDDATACAP_DELAY register field. */
#define ALT_QSPI_RDDATACAP_DELAY_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_QSPI_RDDATACAP_DELAY register field. */
#define ALT_QSPI_RDDATACAP_DELAY_MSB        4
/* The width in bits of the ALT_QSPI_RDDATACAP_DELAY register field. */
#define ALT_QSPI_RDDATACAP_DELAY_WIDTH      4
/* The mask used to set the ALT_QSPI_RDDATACAP_DELAY register field value. */
#define ALT_QSPI_RDDATACAP_DELAY_SET_MSK    0x0000001e
/* The mask used to clear the ALT_QSPI_RDDATACAP_DELAY register field value. */
#define ALT_QSPI_RDDATACAP_DELAY_CLR_MSK    0xffffffe1
/* The reset value of the ALT_QSPI_RDDATACAP_DELAY register field. */
#define ALT_QSPI_RDDATACAP_DELAY_RESET      0x0
/* Extracts the ALT_QSPI_RDDATACAP_DELAY field value from a register. */
#define ALT_QSPI_RDDATACAP_DELAY_GET(value) (((value) & 0x0000001e) >> 1)
/* Produces a ALT_QSPI_RDDATACAP_DELAY register field value suitable for setting the register. */
#define ALT_QSPI_RDDATACAP_DELAY_SET(value) (((value) << 1) & 0x0000001e)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_RDDATACAP.
 */
struct ALT_QSPI_RDDATACAP_s
{
    uint32_t  byp   :  1;  /* Bypass */
    uint32_t  delay :  4;  /* Read Delay */
    uint32_t        : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_RDDATACAP. */
typedef volatile struct ALT_QSPI_RDDATACAP_s  ALT_QSPI_RDDATACAP_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_RDDATACAP register from the beginning of the component. */
#define ALT_QSPI_RDDATACAP_OFST        0x10

/*
 * Register : Device Size Register - devsz
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                    
 * :--------|:-------|:------|:--------------------------------
 *  [3:0]   | RW     | 0x2   | Number of address Bytes        
 *  [15:4]  | RW     | 0x100 | Number of Bytes per Device Page
 *  [20:16] | RW     | 0x10  | Number of Bytes per Block      
 *  [31:21] | ???    | 0x0   | *UNDEFINED*                    
 * 
 */
/*
 * Field : Number of address Bytes - numaddrbytes
 * 
 * Number of address bytes. A value of 0 indicates 1 byte.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_DEVSZ_NUMADDRBYTES register field. */
#define ALT_QSPI_DEVSZ_NUMADDRBYTES_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DEVSZ_NUMADDRBYTES register field. */
#define ALT_QSPI_DEVSZ_NUMADDRBYTES_MSB        3
/* The width in bits of the ALT_QSPI_DEVSZ_NUMADDRBYTES register field. */
#define ALT_QSPI_DEVSZ_NUMADDRBYTES_WIDTH      4
/* The mask used to set the ALT_QSPI_DEVSZ_NUMADDRBYTES register field value. */
#define ALT_QSPI_DEVSZ_NUMADDRBYTES_SET_MSK    0x0000000f
/* The mask used to clear the ALT_QSPI_DEVSZ_NUMADDRBYTES register field value. */
#define ALT_QSPI_DEVSZ_NUMADDRBYTES_CLR_MSK    0xfffffff0
/* The reset value of the ALT_QSPI_DEVSZ_NUMADDRBYTES register field. */
#define ALT_QSPI_DEVSZ_NUMADDRBYTES_RESET      0x2
/* Extracts the ALT_QSPI_DEVSZ_NUMADDRBYTES field value from a register. */
#define ALT_QSPI_DEVSZ_NUMADDRBYTES_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_QSPI_DEVSZ_NUMADDRBYTES register field value suitable for setting the register. */
#define ALT_QSPI_DEVSZ_NUMADDRBYTES_SET(value) (((value) << 0) & 0x0000000f)

/*
 * Field : Number of Bytes per Device Page - bytesperdevicepage
 * 
 * Number of bytes per device page. This is required by the controller for
 * performing FLASH writes up to and across page boundaries.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE register field. */
#define ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE register field. */
#define ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE_MSB        15
/* The width in bits of the ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE register field. */
#define ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE_WIDTH      12
/* The mask used to set the ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE register field value. */
#define ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE_SET_MSK    0x0000fff0
/* The mask used to clear the ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE register field value. */
#define ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE_CLR_MSK    0xffff000f
/* The reset value of the ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE register field. */
#define ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE_RESET      0x100
/* Extracts the ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE field value from a register. */
#define ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE_GET(value) (((value) & 0x0000fff0) >> 4)
/* Produces a ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE register field value suitable for setting the register. */
#define ALT_QSPI_DEVSZ_BYTESPERDEVICEPAGE_SET(value) (((value) << 4) & 0x0000fff0)

/*
 * Field : Number of Bytes per Block - bytespersubsector
 * 
 * Number of bytes per Block. This is required by the controller for performing the
 * write protection logic. The number of bytes per block must be a power of 2
 * number.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR register field. */
#define ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR register field. */
#define ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR_MSB        20
/* The width in bits of the ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR register field. */
#define ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR_WIDTH      5
/* The mask used to set the ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR register field value. */
#define ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR_SET_MSK    0x001f0000
/* The mask used to clear the ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR register field value. */
#define ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR_CLR_MSK    0xffe0ffff
/* The reset value of the ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR register field. */
#define ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR_RESET      0x10
/* Extracts the ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR field value from a register. */
#define ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR_GET(value) (((value) & 0x001f0000) >> 16)
/* Produces a ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR register field value suitable for setting the register. */
#define ALT_QSPI_DEVSZ_BYTESPERSUBSECTOR_SET(value) (((value) << 16) & 0x001f0000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_DEVSZ.
 */
struct ALT_QSPI_DEVSZ_s
{
    uint32_t  numaddrbytes       :  4;  /* Number of address Bytes */
    uint32_t  bytesperdevicepage : 12;  /* Number of Bytes per Device Page */
    uint32_t  bytespersubsector  :  5;  /* Number of Bytes per Block */
    uint32_t                     : 11;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_DEVSZ. */
typedef volatile struct ALT_QSPI_DEVSZ_s  ALT_QSPI_DEVSZ_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_DEVSZ register from the beginning of the component. */
#define ALT_QSPI_DEVSZ_OFST        0x14

/*
 * Register : SRAM Partition Register - srampart
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                 
 * :-------|:-------|:------|:-----------------------------
 *  [6:0]  | RW     | 0x40  | Indirect Read Partition Size
 *  [31:7] | ???    | 0x0   | *UNDEFINED*                 
 * 
 */
/*
 * Field : Indirect Read Partition Size - addr
 * 
 * Defines the size of the indirect read partition in the SRAM, in units of SRAM
 * locations. By default, half of the SRAM is reserved for indirect read operations
 * and half for indirect write operations.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_SRAMPART_ADDR register field. */
#define ALT_QSPI_SRAMPART_ADDR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_SRAMPART_ADDR register field. */
#define ALT_QSPI_SRAMPART_ADDR_MSB        6
/* The width in bits of the ALT_QSPI_SRAMPART_ADDR register field. */
#define ALT_QSPI_SRAMPART_ADDR_WIDTH      7
/* The mask used to set the ALT_QSPI_SRAMPART_ADDR register field value. */
#define ALT_QSPI_SRAMPART_ADDR_SET_MSK    0x0000007f
/* The mask used to clear the ALT_QSPI_SRAMPART_ADDR register field value. */
#define ALT_QSPI_SRAMPART_ADDR_CLR_MSK    0xffffff80
/* The reset value of the ALT_QSPI_SRAMPART_ADDR register field. */
#define ALT_QSPI_SRAMPART_ADDR_RESET      0x40
/* Extracts the ALT_QSPI_SRAMPART_ADDR field value from a register. */
#define ALT_QSPI_SRAMPART_ADDR_GET(value) (((value) & 0x0000007f) >> 0)
/* Produces a ALT_QSPI_SRAMPART_ADDR register field value suitable for setting the register. */
#define ALT_QSPI_SRAMPART_ADDR_SET(value) (((value) << 0) & 0x0000007f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_SRAMPART.
 */
struct ALT_QSPI_SRAMPART_s
{
    uint32_t  addr :  7;  /* Indirect Read Partition Size */
    uint32_t       : 25;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_SRAMPART. */
typedef volatile struct ALT_QSPI_SRAMPART_s  ALT_QSPI_SRAMPART_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_SRAMPART register from the beginning of the component. */
#define ALT_QSPI_SRAMPART_OFST        0x18

/*
 * Register : Indirect AHB Address Trigger Register - indaddrtrig
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description    
 * :-------|:-------|:------|:----------------
 *  [31:0] | RW     | 0x0   | Trigger Address
 * 
 */
/*
 * Field : Trigger Address - addr
 * 
 * This is the base address that will be used by the AHB controller. When the
 * incoming AHB read access address matches a range of addresses from this trigger
 * address to the trigger address + 15, then the AHB request will be completed by
 * fetching data from the Indirect Controllers SRAM.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDADDRTRIG_ADDR register field. */
#define ALT_QSPI_INDADDRTRIG_ADDR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDADDRTRIG_ADDR register field. */
#define ALT_QSPI_INDADDRTRIG_ADDR_MSB        31
/* The width in bits of the ALT_QSPI_INDADDRTRIG_ADDR register field. */
#define ALT_QSPI_INDADDRTRIG_ADDR_WIDTH      32
/* The mask used to set the ALT_QSPI_INDADDRTRIG_ADDR register field value. */
#define ALT_QSPI_INDADDRTRIG_ADDR_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_INDADDRTRIG_ADDR register field value. */
#define ALT_QSPI_INDADDRTRIG_ADDR_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_INDADDRTRIG_ADDR register field. */
#define ALT_QSPI_INDADDRTRIG_ADDR_RESET      0x0
/* Extracts the ALT_QSPI_INDADDRTRIG_ADDR field value from a register. */
#define ALT_QSPI_INDADDRTRIG_ADDR_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_INDADDRTRIG_ADDR register field value suitable for setting the register. */
#define ALT_QSPI_INDADDRTRIG_ADDR_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_INDADDRTRIG.
 */
struct ALT_QSPI_INDADDRTRIG_s
{
    uint32_t  addr : 32;  /* Trigger Address */
};

/* The typedef declaration for register ALT_QSPI_INDADDRTRIG. */
typedef volatile struct ALT_QSPI_INDADDRTRIG_s  ALT_QSPI_INDADDRTRIG_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_INDADDRTRIG register from the beginning of the component. */
#define ALT_QSPI_INDADDRTRIG_OFST        0x1c

/*
 * Register : DMA Peripheral Register - dmaper
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description           
 * :--------|:-------|:------|:-----------------------
 *  [3:0]   | RW     | 0x0   | Number of Single Bytes
 *  [7:4]   | ???    | 0x0   | *UNDEFINED*           
 *  [11:8]  | RW     | 0x0   | Number of Burst Bytes 
 *  [31:12] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : Number of Single Bytes - numsglreqbytes
 * 
 * Number of bytes in a single type request on the DMA peripheral request. A
 * programmed value of 0 represents a single byte. This should be setup before
 * starting the indirect read or write operation. The actual number of bytes used
 * is 2**(value in this register) which will simplify implementation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_DMAPER_NUMSGLREQBYTES register field. */
#define ALT_QSPI_DMAPER_NUMSGLREQBYTES_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DMAPER_NUMSGLREQBYTES register field. */
#define ALT_QSPI_DMAPER_NUMSGLREQBYTES_MSB        3
/* The width in bits of the ALT_QSPI_DMAPER_NUMSGLREQBYTES register field. */
#define ALT_QSPI_DMAPER_NUMSGLREQBYTES_WIDTH      4
/* The mask used to set the ALT_QSPI_DMAPER_NUMSGLREQBYTES register field value. */
#define ALT_QSPI_DMAPER_NUMSGLREQBYTES_SET_MSK    0x0000000f
/* The mask used to clear the ALT_QSPI_DMAPER_NUMSGLREQBYTES register field value. */
#define ALT_QSPI_DMAPER_NUMSGLREQBYTES_CLR_MSK    0xfffffff0
/* The reset value of the ALT_QSPI_DMAPER_NUMSGLREQBYTES register field. */
#define ALT_QSPI_DMAPER_NUMSGLREQBYTES_RESET      0x0
/* Extracts the ALT_QSPI_DMAPER_NUMSGLREQBYTES field value from a register. */
#define ALT_QSPI_DMAPER_NUMSGLREQBYTES_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_QSPI_DMAPER_NUMSGLREQBYTES register field value suitable for setting the register. */
#define ALT_QSPI_DMAPER_NUMSGLREQBYTES_SET(value) (((value) << 0) & 0x0000000f)

/*
 * Field : Number of Burst Bytes - numburstreqbytes
 * 
 * Number of bytes in a burst type request on the DMA peripheral request. A
 * programmed value of 0 represents a single byte. This should be setup before
 * starting the indirect read or write operation. The actual number of bytes used
 * is 2**(value in this register) which will simplify implementation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_DMAPER_NUMBURSTREQBYTES register field. */
#define ALT_QSPI_DMAPER_NUMBURSTREQBYTES_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_QSPI_DMAPER_NUMBURSTREQBYTES register field. */
#define ALT_QSPI_DMAPER_NUMBURSTREQBYTES_MSB        11
/* The width in bits of the ALT_QSPI_DMAPER_NUMBURSTREQBYTES register field. */
#define ALT_QSPI_DMAPER_NUMBURSTREQBYTES_WIDTH      4
/* The mask used to set the ALT_QSPI_DMAPER_NUMBURSTREQBYTES register field value. */
#define ALT_QSPI_DMAPER_NUMBURSTREQBYTES_SET_MSK    0x00000f00
/* The mask used to clear the ALT_QSPI_DMAPER_NUMBURSTREQBYTES register field value. */
#define ALT_QSPI_DMAPER_NUMBURSTREQBYTES_CLR_MSK    0xfffff0ff
/* The reset value of the ALT_QSPI_DMAPER_NUMBURSTREQBYTES register field. */
#define ALT_QSPI_DMAPER_NUMBURSTREQBYTES_RESET      0x0
/* Extracts the ALT_QSPI_DMAPER_NUMBURSTREQBYTES field value from a register. */
#define ALT_QSPI_DMAPER_NUMBURSTREQBYTES_GET(value) (((value) & 0x00000f00) >> 8)
/* Produces a ALT_QSPI_DMAPER_NUMBURSTREQBYTES register field value suitable for setting the register. */
#define ALT_QSPI_DMAPER_NUMBURSTREQBYTES_SET(value) (((value) << 8) & 0x00000f00)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_DMAPER.
 */
struct ALT_QSPI_DMAPER_s
{
    uint32_t  numsglreqbytes   :  4;  /* Number of Single Bytes */
    uint32_t                   :  4;  /* *UNDEFINED* */
    uint32_t  numburstreqbytes :  4;  /* Number of Burst Bytes */
    uint32_t                   : 20;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_DMAPER. */
typedef volatile struct ALT_QSPI_DMAPER_s  ALT_QSPI_DMAPER_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_DMAPER register from the beginning of the component. */
#define ALT_QSPI_DMAPER_OFST        0x20

/*
 * Register : Remap Address Register - remapaddr
 * 
 * This register is used to remap an incoming AHB address to a different address
 * used by the FLASH device.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description         
 * :-------|:-------|:------|:---------------------
 *  [31:0] | RW     | 0x0   | Remap Address Offset
 * 
 */
/*
 * Field : Remap Address Offset - value
 * 
 * This offset is added to the incoming AHB address to determine the address used
 * by the FLASH device.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_REMAPADDR_VALUE register field. */
#define ALT_QSPI_REMAPADDR_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_REMAPADDR_VALUE register field. */
#define ALT_QSPI_REMAPADDR_VALUE_MSB        31
/* The width in bits of the ALT_QSPI_REMAPADDR_VALUE register field. */
#define ALT_QSPI_REMAPADDR_VALUE_WIDTH      32
/* The mask used to set the ALT_QSPI_REMAPADDR_VALUE register field value. */
#define ALT_QSPI_REMAPADDR_VALUE_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_REMAPADDR_VALUE register field value. */
#define ALT_QSPI_REMAPADDR_VALUE_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_REMAPADDR_VALUE register field. */
#define ALT_QSPI_REMAPADDR_VALUE_RESET      0x0
/* Extracts the ALT_QSPI_REMAPADDR_VALUE field value from a register. */
#define ALT_QSPI_REMAPADDR_VALUE_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_REMAPADDR_VALUE register field value suitable for setting the register. */
#define ALT_QSPI_REMAPADDR_VALUE_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_REMAPADDR.
 */
struct ALT_QSPI_REMAPADDR_s
{
    uint32_t  value : 32;  /* Remap Address Offset */
};

/* The typedef declaration for register ALT_QSPI_REMAPADDR. */
typedef volatile struct ALT_QSPI_REMAPADDR_s  ALT_QSPI_REMAPADDR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_REMAPADDR register from the beginning of the component. */
#define ALT_QSPI_REMAPADDR_OFST        0x24

/*
 * Register : Mode Bit Register - modebit
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [7:0]  | RW     | 0x0   | Mode       
 *  [31:8] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Mode - mode
 * 
 * These are the 8 mode bits that are sent to the device following the address
 * bytes if mode bit transmission has been enabled.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_MODBIT_MOD register field. */
#define ALT_QSPI_MODBIT_MOD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_MODBIT_MOD register field. */
#define ALT_QSPI_MODBIT_MOD_MSB        7
/* The width in bits of the ALT_QSPI_MODBIT_MOD register field. */
#define ALT_QSPI_MODBIT_MOD_WIDTH      8
/* The mask used to set the ALT_QSPI_MODBIT_MOD register field value. */
#define ALT_QSPI_MODBIT_MOD_SET_MSK    0x000000ff
/* The mask used to clear the ALT_QSPI_MODBIT_MOD register field value. */
#define ALT_QSPI_MODBIT_MOD_CLR_MSK    0xffffff00
/* The reset value of the ALT_QSPI_MODBIT_MOD register field. */
#define ALT_QSPI_MODBIT_MOD_RESET      0x0
/* Extracts the ALT_QSPI_MODBIT_MOD field value from a register. */
#define ALT_QSPI_MODBIT_MOD_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_QSPI_MODBIT_MOD register field value suitable for setting the register. */
#define ALT_QSPI_MODBIT_MOD_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_MODBIT.
 */
struct ALT_QSPI_MODBIT_s
{
    uint32_t  mode :  8;  /* Mode */
    uint32_t       : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_MODBIT. */
typedef volatile struct ALT_QSPI_MODBIT_s  ALT_QSPI_MODBIT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_MODBIT register from the beginning of the component. */
#define ALT_QSPI_MODBIT_OFST        0x28

/*
 * Register : SRAM Fill Register - sramfill
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                                       
 * :--------|:-------|:------|:-------------------------------------------------------------------
 *  [15:0]  | R      | 0x0   | SRAM Fill Level (Indirect Read Partition). In units of SRAM WORDS 
 *  [31:16] | R      | 0x0   | SRAM Fill Level (Indirect Write Partition). In units of SRAM WORDS
 * 
 */
/*
 * Field : SRAM Fill Level (Indirect Read Partition). In units of SRAM WORDS - indrdpart
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_SRAMFILL_INDRDPART register field. */
#define ALT_QSPI_SRAMFILL_INDRDPART_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_SRAMFILL_INDRDPART register field. */
#define ALT_QSPI_SRAMFILL_INDRDPART_MSB        15
/* The width in bits of the ALT_QSPI_SRAMFILL_INDRDPART register field. */
#define ALT_QSPI_SRAMFILL_INDRDPART_WIDTH      16
/* The mask used to set the ALT_QSPI_SRAMFILL_INDRDPART register field value. */
#define ALT_QSPI_SRAMFILL_INDRDPART_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_QSPI_SRAMFILL_INDRDPART register field value. */
#define ALT_QSPI_SRAMFILL_INDRDPART_CLR_MSK    0xffff0000
/* The reset value of the ALT_QSPI_SRAMFILL_INDRDPART register field. */
#define ALT_QSPI_SRAMFILL_INDRDPART_RESET      0x0
/* Extracts the ALT_QSPI_SRAMFILL_INDRDPART field value from a register. */
#define ALT_QSPI_SRAMFILL_INDRDPART_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_QSPI_SRAMFILL_INDRDPART register field value suitable for setting the register. */
#define ALT_QSPI_SRAMFILL_INDRDPART_SET(value) (((value) << 0) & 0x0000ffff)

/*
 * Field : SRAM Fill Level (Indirect Write Partition). In units of SRAM WORDS - indwrpart
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_SRAMFILL_INDWRPART register field. */
#define ALT_QSPI_SRAMFILL_INDWRPART_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_QSPI_SRAMFILL_INDWRPART register field. */
#define ALT_QSPI_SRAMFILL_INDWRPART_MSB        31
/* The width in bits of the ALT_QSPI_SRAMFILL_INDWRPART register field. */
#define ALT_QSPI_SRAMFILL_INDWRPART_WIDTH      16
/* The mask used to set the ALT_QSPI_SRAMFILL_INDWRPART register field value. */
#define ALT_QSPI_SRAMFILL_INDWRPART_SET_MSK    0xffff0000
/* The mask used to clear the ALT_QSPI_SRAMFILL_INDWRPART register field value. */
#define ALT_QSPI_SRAMFILL_INDWRPART_CLR_MSK    0x0000ffff
/* The reset value of the ALT_QSPI_SRAMFILL_INDWRPART register field. */
#define ALT_QSPI_SRAMFILL_INDWRPART_RESET      0x0
/* Extracts the ALT_QSPI_SRAMFILL_INDWRPART field value from a register. */
#define ALT_QSPI_SRAMFILL_INDWRPART_GET(value) (((value) & 0xffff0000) >> 16)
/* Produces a ALT_QSPI_SRAMFILL_INDWRPART register field value suitable for setting the register. */
#define ALT_QSPI_SRAMFILL_INDWRPART_SET(value) (((value) << 16) & 0xffff0000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_SRAMFILL.
 */
struct ALT_QSPI_SRAMFILL_s
{
    const uint32_t  indrdpart : 16;  /* SRAM Fill Level (Indirect Read Partition). In units of SRAM WORDS */
    const uint32_t  indwrpart : 16;  /* SRAM Fill Level (Indirect Write Partition). In units of SRAM WORDS */
};

/* The typedef declaration for register ALT_QSPI_SRAMFILL. */
typedef volatile struct ALT_QSPI_SRAMFILL_s  ALT_QSPI_SRAMFILL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_SRAMFILL register from the beginning of the component. */
#define ALT_QSPI_SRAMFILL_OFST        0x2c

/*
 * Register : TX Threshold Register - txthresh
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [3:0]  | RW     | 0x1   | Level      
 *  [31:4] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Level - level
 * 
 * Defines the level at which the transmit FIFO not full interrupt is generated
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_TXTHRESH_LEVEL register field. */
#define ALT_QSPI_TXTHRESH_LEVEL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_TXTHRESH_LEVEL register field. */
#define ALT_QSPI_TXTHRESH_LEVEL_MSB        3
/* The width in bits of the ALT_QSPI_TXTHRESH_LEVEL register field. */
#define ALT_QSPI_TXTHRESH_LEVEL_WIDTH      4
/* The mask used to set the ALT_QSPI_TXTHRESH_LEVEL register field value. */
#define ALT_QSPI_TXTHRESH_LEVEL_SET_MSK    0x0000000f
/* The mask used to clear the ALT_QSPI_TXTHRESH_LEVEL register field value. */
#define ALT_QSPI_TXTHRESH_LEVEL_CLR_MSK    0xfffffff0
/* The reset value of the ALT_QSPI_TXTHRESH_LEVEL register field. */
#define ALT_QSPI_TXTHRESH_LEVEL_RESET      0x1
/* Extracts the ALT_QSPI_TXTHRESH_LEVEL field value from a register. */
#define ALT_QSPI_TXTHRESH_LEVEL_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_QSPI_TXTHRESH_LEVEL register field value suitable for setting the register. */
#define ALT_QSPI_TXTHRESH_LEVEL_SET(value) (((value) << 0) & 0x0000000f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_TXTHRESH.
 */
struct ALT_QSPI_TXTHRESH_s
{
    uint32_t  level :  4;  /* Level */
    uint32_t        : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_TXTHRESH. */
typedef volatile struct ALT_QSPI_TXTHRESH_s  ALT_QSPI_TXTHRESH_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_TXTHRESH register from the beginning of the component. */
#define ALT_QSPI_TXTHRESH_OFST        0x30

/*
 * Register : RX Threshold Register - rxthresh
 * 
 * Device Instruction Register
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [3:0]  | RW     | 0x1   | Level      
 *  [31:4] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Level - level
 * 
 * Defines the level at which the receive FIFO not empty interrupt is generated
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_RXTHRESH_LEVEL register field. */
#define ALT_QSPI_RXTHRESH_LEVEL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_RXTHRESH_LEVEL register field. */
#define ALT_QSPI_RXTHRESH_LEVEL_MSB        3
/* The width in bits of the ALT_QSPI_RXTHRESH_LEVEL register field. */
#define ALT_QSPI_RXTHRESH_LEVEL_WIDTH      4
/* The mask used to set the ALT_QSPI_RXTHRESH_LEVEL register field value. */
#define ALT_QSPI_RXTHRESH_LEVEL_SET_MSK    0x0000000f
/* The mask used to clear the ALT_QSPI_RXTHRESH_LEVEL register field value. */
#define ALT_QSPI_RXTHRESH_LEVEL_CLR_MSK    0xfffffff0
/* The reset value of the ALT_QSPI_RXTHRESH_LEVEL register field. */
#define ALT_QSPI_RXTHRESH_LEVEL_RESET      0x1
/* Extracts the ALT_QSPI_RXTHRESH_LEVEL field value from a register. */
#define ALT_QSPI_RXTHRESH_LEVEL_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_QSPI_RXTHRESH_LEVEL register field value suitable for setting the register. */
#define ALT_QSPI_RXTHRESH_LEVEL_SET(value) (((value) << 0) & 0x0000000f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_RXTHRESH.
 */
struct ALT_QSPI_RXTHRESH_s
{
    uint32_t  level :  4;  /* Level */
    uint32_t        : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_RXTHRESH. */
typedef volatile struct ALT_QSPI_RXTHRESH_s  ALT_QSPI_RXTHRESH_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_RXTHRESH register from the beginning of the component. */
#define ALT_QSPI_RXTHRESH_OFST        0x34

/*
 * Register : Interrupt Status Register - irqstat
 * 
 * The status fields in this register are set when the described event occurs and
 * the interrupt is enabled in the mask register. When any of these bit fields are
 * set, the interrupt output is asserted high. The fields are each cleared by
 * writing a 1 to the field. Note that bit fields 7 thru 11 are only valid when
 * legacy SPI mode is active.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                        
 * :--------|:-------|:------|:------------------------------------
 *  [0]     | ???    | 0x0   | *UNDEFINED*                        
 *  [1]     | RW     | 0x0   | Underflow Detected                 
 *  [2]     | RW     | 0x0   | Indirect Operation Complete        
 *  [3]     | RW     | 0x0   | Indirect Read Reject               
 *  [4]     | RW     | 0x0   | Protected Area Write Attempt       
 *  [5]     | RW     | 0x0   | Illegal AHB Access Detected        
 *  [6]     | RW     | 0x0   | Transfer Watermark Reached         
 *  [7]     | RW     | 0x0   | Receive Overflow                   
 *  [8]     | RW     | 0x1   | Transmit FIFO Compared to Threshold
 *  [9]     | RW     | 0x0   | Transmit FIFO Full                 
 *  [10]    | RW     | 0x0   | Receive FIFO Compared to Threshold 
 *  [11]    | RW     | 0x0   | Receive FIFO Full                  
 *  [12]    | RW     | 0x0   | Indirect Read Partition overflow   
 *  [31:13] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : Underflow Detected - underflowdet
 * 
 * An underflow is detected when an attempt to transfer data is made when the
 * transmit FIFO is empty. This may occur when the AHB write data is being supplied
 * too slowly to keep up with the requested write operation. This bit is reset only
 * by a system reset and cleared only when the register is read.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                        | Value | Description 
 * :--------------------------------------------|:------|:-------------
 *  ALT_QSPI_IRQSTAT_UNDERFLOWDET_E_UNDERFLOW   | 0x1   | Underflow   
 *  ALT_QSPI_IRQSTAT_UNDERFLOWDET_E_NOUNDERFLOW | 0x0   | No Underflow
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_UNDERFLOWDET
 * 
 * Underflow
 */
#define ALT_QSPI_IRQSTAT_UNDERFLOWDET_E_UNDERFLOW   0x1
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_UNDERFLOWDET
 * 
 * No Underflow
 */
#define ALT_QSPI_IRQSTAT_UNDERFLOWDET_E_NOUNDERFLOW 0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQSTAT_UNDERFLOWDET register field. */
#define ALT_QSPI_IRQSTAT_UNDERFLOWDET_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQSTAT_UNDERFLOWDET register field. */
#define ALT_QSPI_IRQSTAT_UNDERFLOWDET_MSB        1
/* The width in bits of the ALT_QSPI_IRQSTAT_UNDERFLOWDET register field. */
#define ALT_QSPI_IRQSTAT_UNDERFLOWDET_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQSTAT_UNDERFLOWDET register field value. */
#define ALT_QSPI_IRQSTAT_UNDERFLOWDET_SET_MSK    0x00000002
/* The mask used to clear the ALT_QSPI_IRQSTAT_UNDERFLOWDET register field value. */
#define ALT_QSPI_IRQSTAT_UNDERFLOWDET_CLR_MSK    0xfffffffd
/* The reset value of the ALT_QSPI_IRQSTAT_UNDERFLOWDET register field. */
#define ALT_QSPI_IRQSTAT_UNDERFLOWDET_RESET      0x0
/* Extracts the ALT_QSPI_IRQSTAT_UNDERFLOWDET field value from a register. */
#define ALT_QSPI_IRQSTAT_UNDERFLOWDET_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_QSPI_IRQSTAT_UNDERFLOWDET register field value suitable for setting the register. */
#define ALT_QSPI_IRQSTAT_UNDERFLOWDET_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Indirect Operation Complete - indopdone
 * 
 * Controller has completed last triggered indirect operation
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description                 
 * :------------------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQSTAT_INDOPDONE_E_INDIRECTOP   | 0x1   | Completed Indirect Operation
 *  ALT_QSPI_IRQSTAT_INDOPDONE_E_NOINDIRECTOP | 0x0   | No Indirect Operation       
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_INDOPDONE
 * 
 * Completed Indirect Operation
 */
#define ALT_QSPI_IRQSTAT_INDOPDONE_E_INDIRECTOP     0x1
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_INDOPDONE
 * 
 * No Indirect Operation
 */
#define ALT_QSPI_IRQSTAT_INDOPDONE_E_NOINDIRECTOP   0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQSTAT_INDOPDONE register field. */
#define ALT_QSPI_IRQSTAT_INDOPDONE_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQSTAT_INDOPDONE register field. */
#define ALT_QSPI_IRQSTAT_INDOPDONE_MSB        2
/* The width in bits of the ALT_QSPI_IRQSTAT_INDOPDONE register field. */
#define ALT_QSPI_IRQSTAT_INDOPDONE_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQSTAT_INDOPDONE register field value. */
#define ALT_QSPI_IRQSTAT_INDOPDONE_SET_MSK    0x00000004
/* The mask used to clear the ALT_QSPI_IRQSTAT_INDOPDONE register field value. */
#define ALT_QSPI_IRQSTAT_INDOPDONE_CLR_MSK    0xfffffffb
/* The reset value of the ALT_QSPI_IRQSTAT_INDOPDONE register field. */
#define ALT_QSPI_IRQSTAT_INDOPDONE_RESET      0x0
/* Extracts the ALT_QSPI_IRQSTAT_INDOPDONE field value from a register. */
#define ALT_QSPI_IRQSTAT_INDOPDONE_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_QSPI_IRQSTAT_INDOPDONE register field value suitable for setting the register. */
#define ALT_QSPI_IRQSTAT_INDOPDONE_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Indirect Read Reject - indrdreject
 * 
 * Indirect operation was requested but could not be accepted. Two indirect
 * operations already in storage.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                         | Value | Description                 
 * :---------------------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQSTAT_INDRDREJECT_E_INDIRECTREQ   | 0x1   | Indirect Operation Requested
 *  ALT_QSPI_IRQSTAT_INDRDREJECT_E_NOINDIRECTREQ | 0x0   | No Indirect Operation       
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_INDRDREJECT
 * 
 * Indirect Operation Requested
 */
#define ALT_QSPI_IRQSTAT_INDRDREJECT_E_INDIRECTREQ      0x1
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_INDRDREJECT
 * 
 * No Indirect Operation
 */
#define ALT_QSPI_IRQSTAT_INDRDREJECT_E_NOINDIRECTREQ    0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQSTAT_INDRDREJECT register field. */
#define ALT_QSPI_IRQSTAT_INDRDREJECT_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQSTAT_INDRDREJECT register field. */
#define ALT_QSPI_IRQSTAT_INDRDREJECT_MSB        3
/* The width in bits of the ALT_QSPI_IRQSTAT_INDRDREJECT register field. */
#define ALT_QSPI_IRQSTAT_INDRDREJECT_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQSTAT_INDRDREJECT register field value. */
#define ALT_QSPI_IRQSTAT_INDRDREJECT_SET_MSK    0x00000008
/* The mask used to clear the ALT_QSPI_IRQSTAT_INDRDREJECT register field value. */
#define ALT_QSPI_IRQSTAT_INDRDREJECT_CLR_MSK    0xfffffff7
/* The reset value of the ALT_QSPI_IRQSTAT_INDRDREJECT register field. */
#define ALT_QSPI_IRQSTAT_INDRDREJECT_RESET      0x0
/* Extracts the ALT_QSPI_IRQSTAT_INDRDREJECT field value from a register. */
#define ALT_QSPI_IRQSTAT_INDRDREJECT_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_QSPI_IRQSTAT_INDRDREJECT register field value suitable for setting the register. */
#define ALT_QSPI_IRQSTAT_INDRDREJECT_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Protected Area Write Attempt - protwrattempt
 * 
 * Write to protected area was attempted and rejected.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description                    
 * :------------------------------------------|:------|:--------------------------------
 *  ALT_QSPI_IRQSTAT_PROTWRATTEMPT_E_WRPROT   | 0x1   | Write Attempt to protected area
 *  ALT_QSPI_IRQSTAT_PROTWRATTEMPT_E_NOWRPROT | 0x0   | No Write Attempt               
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_PROTWRATTEMPT
 * 
 * Write Attempt to protected area
 */
#define ALT_QSPI_IRQSTAT_PROTWRATTEMPT_E_WRPROT     0x1
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_PROTWRATTEMPT
 * 
 * No Write Attempt
 */
#define ALT_QSPI_IRQSTAT_PROTWRATTEMPT_E_NOWRPROT   0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQSTAT_PROTWRATTEMPT register field. */
#define ALT_QSPI_IRQSTAT_PROTWRATTEMPT_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQSTAT_PROTWRATTEMPT register field. */
#define ALT_QSPI_IRQSTAT_PROTWRATTEMPT_MSB        4
/* The width in bits of the ALT_QSPI_IRQSTAT_PROTWRATTEMPT register field. */
#define ALT_QSPI_IRQSTAT_PROTWRATTEMPT_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQSTAT_PROTWRATTEMPT register field value. */
#define ALT_QSPI_IRQSTAT_PROTWRATTEMPT_SET_MSK    0x00000010
/* The mask used to clear the ALT_QSPI_IRQSTAT_PROTWRATTEMPT register field value. */
#define ALT_QSPI_IRQSTAT_PROTWRATTEMPT_CLR_MSK    0xffffffef
/* The reset value of the ALT_QSPI_IRQSTAT_PROTWRATTEMPT register field. */
#define ALT_QSPI_IRQSTAT_PROTWRATTEMPT_RESET      0x0
/* Extracts the ALT_QSPI_IRQSTAT_PROTWRATTEMPT field value from a register. */
#define ALT_QSPI_IRQSTAT_PROTWRATTEMPT_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_QSPI_IRQSTAT_PROTWRATTEMPT register field value suitable for setting the register. */
#define ALT_QSPI_IRQSTAT_PROTWRATTEMPT_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Illegal AHB Access Detected - illegalacc
 * 
 * Illegal AHB access has been detected. AHB wrapping bursts and the use of
 * SPLIT/RETRY accesses will cause this error interrupt to trigger.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                       | Value | Description           
 * :-------------------------------------------|:------|:-----------------------
 *  ALT_QSPI_IRQSTAT_ILLEGALACC_E_ILLEGALAHB   | 0x1   | Illegal AHB attempt   
 *  ALT_QSPI_IRQSTAT_ILLEGALACC_E_NOILLEGALAHB | 0x0   | No Illegal AHB attempt
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_ILLEGALACC
 * 
 * Illegal AHB attempt
 */
#define ALT_QSPI_IRQSTAT_ILLEGALACC_E_ILLEGALAHB    0x1
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_ILLEGALACC
 * 
 * No Illegal AHB attempt
 */
#define ALT_QSPI_IRQSTAT_ILLEGALACC_E_NOILLEGALAHB  0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQSTAT_ILLEGALACC register field. */
#define ALT_QSPI_IRQSTAT_ILLEGALACC_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQSTAT_ILLEGALACC register field. */
#define ALT_QSPI_IRQSTAT_ILLEGALACC_MSB        5
/* The width in bits of the ALT_QSPI_IRQSTAT_ILLEGALACC register field. */
#define ALT_QSPI_IRQSTAT_ILLEGALACC_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQSTAT_ILLEGALACC register field value. */
#define ALT_QSPI_IRQSTAT_ILLEGALACC_SET_MSK    0x00000020
/* The mask used to clear the ALT_QSPI_IRQSTAT_ILLEGALACC register field value. */
#define ALT_QSPI_IRQSTAT_ILLEGALACC_CLR_MSK    0xffffffdf
/* The reset value of the ALT_QSPI_IRQSTAT_ILLEGALACC register field. */
#define ALT_QSPI_IRQSTAT_ILLEGALACC_RESET      0x0
/* Extracts the ALT_QSPI_IRQSTAT_ILLEGALACC field value from a register. */
#define ALT_QSPI_IRQSTAT_ILLEGALACC_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_QSPI_IRQSTAT_ILLEGALACC register field value suitable for setting the register. */
#define ALT_QSPI_IRQSTAT_ILLEGALACC_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Transfer Watermark Reached - indxfrlvl
 * 
 * Indirect Transfer Watermark Level Reached
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                    | Value | Description           
 * :----------------------------------------|:------|:-----------------------
 *  ALT_QSPI_IRQSTAT_INDXFRLVL_E_WATERLEVL  | 0x1   | Water level reached   
 *  ALT_QSPI_IRQSTAT_INDXFRLVL_E_NOWATERLVL | 0x0   | No water level reached
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_INDXFRLVL
 * 
 * Water level reached
 */
#define ALT_QSPI_IRQSTAT_INDXFRLVL_E_WATERLEVL  0x1
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_INDXFRLVL
 * 
 * No water level reached
 */
#define ALT_QSPI_IRQSTAT_INDXFRLVL_E_NOWATERLVL 0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQSTAT_INDXFRLVL register field. */
#define ALT_QSPI_IRQSTAT_INDXFRLVL_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQSTAT_INDXFRLVL register field. */
#define ALT_QSPI_IRQSTAT_INDXFRLVL_MSB        6
/* The width in bits of the ALT_QSPI_IRQSTAT_INDXFRLVL register field. */
#define ALT_QSPI_IRQSTAT_INDXFRLVL_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQSTAT_INDXFRLVL register field value. */
#define ALT_QSPI_IRQSTAT_INDXFRLVL_SET_MSK    0x00000040
/* The mask used to clear the ALT_QSPI_IRQSTAT_INDXFRLVL register field value. */
#define ALT_QSPI_IRQSTAT_INDXFRLVL_CLR_MSK    0xffffffbf
/* The reset value of the ALT_QSPI_IRQSTAT_INDXFRLVL register field. */
#define ALT_QSPI_IRQSTAT_INDXFRLVL_RESET      0x0
/* Extracts the ALT_QSPI_IRQSTAT_INDXFRLVL field value from a register. */
#define ALT_QSPI_IRQSTAT_INDXFRLVL_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_QSPI_IRQSTAT_INDXFRLVL register field value suitable for setting the register. */
#define ALT_QSPI_IRQSTAT_INDXFRLVL_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Receive Overflow - rxover
 * 
 * This should only occur in Legacy SPI mode. Set if an attempt is made to push the
 * RX FIFO when it is full. This bit is reset only by a system reset and cleared
 * only when this register is read. If a new push to the RX FIFO occurs coincident
 * with a register read this flag will remain set. 0 : no overflow has been
 * detected. 1 : an overflow has occurred.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description        
 * :------------------------------------|:------|:--------------------
 *  ALT_QSPI_IRQSTAT_RXOVER_E_RCVOVER   | 0x1   | Receive Overflow   
 *  ALT_QSPI_IRQSTAT_RXOVER_E_NORCVOVER | 0x0   | No Receive Overflow
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_RXOVER
 * 
 * Receive Overflow
 */
#define ALT_QSPI_IRQSTAT_RXOVER_E_RCVOVER   0x1
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_RXOVER
 * 
 * No Receive Overflow
 */
#define ALT_QSPI_IRQSTAT_RXOVER_E_NORCVOVER 0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQSTAT_RXOVER register field. */
#define ALT_QSPI_IRQSTAT_RXOVER_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQSTAT_RXOVER register field. */
#define ALT_QSPI_IRQSTAT_RXOVER_MSB        7
/* The width in bits of the ALT_QSPI_IRQSTAT_RXOVER register field. */
#define ALT_QSPI_IRQSTAT_RXOVER_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQSTAT_RXOVER register field value. */
#define ALT_QSPI_IRQSTAT_RXOVER_SET_MSK    0x00000080
/* The mask used to clear the ALT_QSPI_IRQSTAT_RXOVER register field value. */
#define ALT_QSPI_IRQSTAT_RXOVER_CLR_MSK    0xffffff7f
/* The reset value of the ALT_QSPI_IRQSTAT_RXOVER register field. */
#define ALT_QSPI_IRQSTAT_RXOVER_RESET      0x0
/* Extracts the ALT_QSPI_IRQSTAT_RXOVER field value from a register. */
#define ALT_QSPI_IRQSTAT_RXOVER_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_QSPI_IRQSTAT_RXOVER register field value suitable for setting the register. */
#define ALT_QSPI_IRQSTAT_RXOVER_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Transmit FIFO Compared to Threshold - txthreshcmp
 * 
 * Indicates the number of entries in the transmit FIFO with respect to the
 * threshold specified in the TXTHRESH register. Only relevant in SPI legacy mode.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                 
 * :----------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQSTAT_TXTHRESHCMP_E_GT | 0x0   | FIFO has > TXTHRESH entries 
 *  ALT_QSPI_IRQSTAT_TXTHRESHCMP_E_LE | 0x1   | FIFO has <= TXTHRESH entries
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_TXTHRESHCMP
 * 
 * FIFO has > TXTHRESH entries
 */
#define ALT_QSPI_IRQSTAT_TXTHRESHCMP_E_GT   0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_TXTHRESHCMP
 * 
 * FIFO has <= TXTHRESH entries
 */
#define ALT_QSPI_IRQSTAT_TXTHRESHCMP_E_LE   0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQSTAT_TXTHRESHCMP register field. */
#define ALT_QSPI_IRQSTAT_TXTHRESHCMP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQSTAT_TXTHRESHCMP register field. */
#define ALT_QSPI_IRQSTAT_TXTHRESHCMP_MSB        8
/* The width in bits of the ALT_QSPI_IRQSTAT_TXTHRESHCMP register field. */
#define ALT_QSPI_IRQSTAT_TXTHRESHCMP_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQSTAT_TXTHRESHCMP register field value. */
#define ALT_QSPI_IRQSTAT_TXTHRESHCMP_SET_MSK    0x00000100
/* The mask used to clear the ALT_QSPI_IRQSTAT_TXTHRESHCMP register field value. */
#define ALT_QSPI_IRQSTAT_TXTHRESHCMP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_QSPI_IRQSTAT_TXTHRESHCMP register field. */
#define ALT_QSPI_IRQSTAT_TXTHRESHCMP_RESET      0x1
/* Extracts the ALT_QSPI_IRQSTAT_TXTHRESHCMP field value from a register. */
#define ALT_QSPI_IRQSTAT_TXTHRESHCMP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_QSPI_IRQSTAT_TXTHRESHCMP register field value suitable for setting the register. */
#define ALT_QSPI_IRQSTAT_TXTHRESHCMP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Transmit FIFO Full - txfull
 * 
 * Indicates that the transmit FIFO is full or not. Only relevant in SPI legacy
 * mode.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description           
 * :----------------------------------|:------|:-----------------------
 *  ALT_QSPI_IRQSTAT_TXFULL_E_NOTFULL | 0x0   | Transmit FIFO Not Full
 *  ALT_QSPI_IRQSTAT_TXFULL_E_FULL    | 0x1   | Transmit FIFO Full    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_TXFULL
 * 
 * Transmit FIFO Not Full
 */
#define ALT_QSPI_IRQSTAT_TXFULL_E_NOTFULL   0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_TXFULL
 * 
 * Transmit FIFO Full
 */
#define ALT_QSPI_IRQSTAT_TXFULL_E_FULL      0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQSTAT_TXFULL register field. */
#define ALT_QSPI_IRQSTAT_TXFULL_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQSTAT_TXFULL register field. */
#define ALT_QSPI_IRQSTAT_TXFULL_MSB        9
/* The width in bits of the ALT_QSPI_IRQSTAT_TXFULL register field. */
#define ALT_QSPI_IRQSTAT_TXFULL_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQSTAT_TXFULL register field value. */
#define ALT_QSPI_IRQSTAT_TXFULL_SET_MSK    0x00000200
/* The mask used to clear the ALT_QSPI_IRQSTAT_TXFULL register field value. */
#define ALT_QSPI_IRQSTAT_TXFULL_CLR_MSK    0xfffffdff
/* The reset value of the ALT_QSPI_IRQSTAT_TXFULL register field. */
#define ALT_QSPI_IRQSTAT_TXFULL_RESET      0x0
/* Extracts the ALT_QSPI_IRQSTAT_TXFULL field value from a register. */
#define ALT_QSPI_IRQSTAT_TXFULL_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_QSPI_IRQSTAT_TXFULL register field value suitable for setting the register. */
#define ALT_QSPI_IRQSTAT_TXFULL_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Receive FIFO Compared to Threshold - rxthreshcmp
 * 
 * Indicates the number of entries in the receive FIFO with respect to the
 * threshold specified in the RXTHRESH register. Only relevant in SPI legacy mode.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                 
 * :----------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQSTAT_RXTHRESHCMP_E_LE | 0x0   | FIFO has <= RXTHRESH entries
 *  ALT_QSPI_IRQSTAT_RXTHRESHCMP_E_GT | 0x1   | FIFO has > RXTHRESH entries 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_RXTHRESHCMP
 * 
 * FIFO has <= RXTHRESH entries
 */
#define ALT_QSPI_IRQSTAT_RXTHRESHCMP_E_LE   0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_RXTHRESHCMP
 * 
 * FIFO has > RXTHRESH entries
 */
#define ALT_QSPI_IRQSTAT_RXTHRESHCMP_E_GT   0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQSTAT_RXTHRESHCMP register field. */
#define ALT_QSPI_IRQSTAT_RXTHRESHCMP_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQSTAT_RXTHRESHCMP register field. */
#define ALT_QSPI_IRQSTAT_RXTHRESHCMP_MSB        10
/* The width in bits of the ALT_QSPI_IRQSTAT_RXTHRESHCMP register field. */
#define ALT_QSPI_IRQSTAT_RXTHRESHCMP_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQSTAT_RXTHRESHCMP register field value. */
#define ALT_QSPI_IRQSTAT_RXTHRESHCMP_SET_MSK    0x00000400
/* The mask used to clear the ALT_QSPI_IRQSTAT_RXTHRESHCMP register field value. */
#define ALT_QSPI_IRQSTAT_RXTHRESHCMP_CLR_MSK    0xfffffbff
/* The reset value of the ALT_QSPI_IRQSTAT_RXTHRESHCMP register field. */
#define ALT_QSPI_IRQSTAT_RXTHRESHCMP_RESET      0x0
/* Extracts the ALT_QSPI_IRQSTAT_RXTHRESHCMP field value from a register. */
#define ALT_QSPI_IRQSTAT_RXTHRESHCMP_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_QSPI_IRQSTAT_RXTHRESHCMP register field value suitable for setting the register. */
#define ALT_QSPI_IRQSTAT_RXTHRESHCMP_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Receive FIFO Full - rxfull
 * 
 * Indicates that the receive FIFO is full or not. Only relevant in SPI legacy
 * mode.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description          
 * :----------------------------------|:------|:----------------------
 *  ALT_QSPI_IRQSTAT_RXFULL_E_NOTFULL | 0x0   | Receive FIFO Not Full
 *  ALT_QSPI_IRQSTAT_RXFULL_E_FULL    | 0x1   | Receive FIFO Full    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_RXFULL
 * 
 * Receive FIFO Not Full
 */
#define ALT_QSPI_IRQSTAT_RXFULL_E_NOTFULL   0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_RXFULL
 * 
 * Receive FIFO Full
 */
#define ALT_QSPI_IRQSTAT_RXFULL_E_FULL      0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQSTAT_RXFULL register field. */
#define ALT_QSPI_IRQSTAT_RXFULL_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQSTAT_RXFULL register field. */
#define ALT_QSPI_IRQSTAT_RXFULL_MSB        11
/* The width in bits of the ALT_QSPI_IRQSTAT_RXFULL register field. */
#define ALT_QSPI_IRQSTAT_RXFULL_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQSTAT_RXFULL register field value. */
#define ALT_QSPI_IRQSTAT_RXFULL_SET_MSK    0x00000800
/* The mask used to clear the ALT_QSPI_IRQSTAT_RXFULL register field value. */
#define ALT_QSPI_IRQSTAT_RXFULL_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_QSPI_IRQSTAT_RXFULL register field. */
#define ALT_QSPI_IRQSTAT_RXFULL_RESET      0x0
/* Extracts the ALT_QSPI_IRQSTAT_RXFULL field value from a register. */
#define ALT_QSPI_IRQSTAT_RXFULL_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_QSPI_IRQSTAT_RXFULL register field value suitable for setting the register. */
#define ALT_QSPI_IRQSTAT_RXFULL_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : Indirect Read Partition overflow - indsramfull
 * 
 * Indirect Read Partition of SRAM is full and unable to immediately complete
 * indirect operation
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                         | Value | Description     
 * :---------------------------------------------|:------|:-----------------
 *  ALT_QSPI_IRQSTAT_INDSRAMFULL_E_RDPARTFULL    | 0x1   | SRAM is full    
 *  ALT_QSPI_IRQSTAT_INDSRAMFULL_E_RDPARTNOTFULL | 0x0   | SRAM is not full
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_INDSRAMFULL
 * 
 * SRAM is full
 */
#define ALT_QSPI_IRQSTAT_INDSRAMFULL_E_RDPARTFULL       0x1
/*
 * Enumerated value for register field ALT_QSPI_IRQSTAT_INDSRAMFULL
 * 
 * SRAM is not full
 */
#define ALT_QSPI_IRQSTAT_INDSRAMFULL_E_RDPARTNOTFULL    0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQSTAT_INDSRAMFULL register field. */
#define ALT_QSPI_IRQSTAT_INDSRAMFULL_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQSTAT_INDSRAMFULL register field. */
#define ALT_QSPI_IRQSTAT_INDSRAMFULL_MSB        12
/* The width in bits of the ALT_QSPI_IRQSTAT_INDSRAMFULL register field. */
#define ALT_QSPI_IRQSTAT_INDSRAMFULL_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQSTAT_INDSRAMFULL register field value. */
#define ALT_QSPI_IRQSTAT_INDSRAMFULL_SET_MSK    0x00001000
/* The mask used to clear the ALT_QSPI_IRQSTAT_INDSRAMFULL register field value. */
#define ALT_QSPI_IRQSTAT_INDSRAMFULL_CLR_MSK    0xffffefff
/* The reset value of the ALT_QSPI_IRQSTAT_INDSRAMFULL register field. */
#define ALT_QSPI_IRQSTAT_INDSRAMFULL_RESET      0x0
/* Extracts the ALT_QSPI_IRQSTAT_INDSRAMFULL field value from a register. */
#define ALT_QSPI_IRQSTAT_INDSRAMFULL_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_QSPI_IRQSTAT_INDSRAMFULL register field value suitable for setting the register. */
#define ALT_QSPI_IRQSTAT_INDSRAMFULL_SET(value) (((value) << 12) & 0x00001000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_IRQSTAT.
 */
struct ALT_QSPI_IRQSTAT_s
{
    uint32_t                :  1;  /* *UNDEFINED* */
    uint32_t  underflowdet  :  1;  /* Underflow Detected */
    uint32_t  indopdone     :  1;  /* Indirect Operation Complete */
    uint32_t  indrdreject   :  1;  /* Indirect Read Reject */
    uint32_t  protwrattempt :  1;  /* Protected Area Write Attempt */
    uint32_t  illegalacc    :  1;  /* Illegal AHB Access Detected */
    uint32_t  indxfrlvl     :  1;  /* Transfer Watermark Reached */
    uint32_t  rxover        :  1;  /* Receive Overflow */
    uint32_t  txthreshcmp   :  1;  /* Transmit FIFO Compared to Threshold */
    uint32_t  txfull        :  1;  /* Transmit FIFO Full */
    uint32_t  rxthreshcmp   :  1;  /* Receive FIFO Compared to Threshold */
    uint32_t  rxfull        :  1;  /* Receive FIFO Full */
    uint32_t  indsramfull   :  1;  /* Indirect Read Partition overflow */
    uint32_t                : 19;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_IRQSTAT. */
typedef volatile struct ALT_QSPI_IRQSTAT_s  ALT_QSPI_IRQSTAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_IRQSTAT register from the beginning of the component. */
#define ALT_QSPI_IRQSTAT_OFST        0x40

/*
 * Register : Interrupt Mask - irqmask
 * 
 * If disabled, the interrupt for the corresponding interrupt status register bit
 * is disabled. If enabled, the interrupt for the corresponding interrupt status
 * register bit is enabled.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                          
 * :--------|:-------|:------|:--------------------------------------
 *  [0]     | ???    | 0x0   | *UNDEFINED*                          
 *  [1]     | RW     | 0x0   | Underflow Detected Mask              
 *  [2]     | RW     | 0x0   | Mask                                 
 *  [3]     | RW     | 0x0   | Indirect Read Reject Mask            
 *  [4]     | RW     | 0x0   | Protected Area Write Attempt Mask    
 *  [5]     | RW     | 0x0   | Illegal Access Detected Mask         
 *  [6]     | RW     | 0x0   | Transfer Watermark Breach Mask       
 *  [7]     | RW     | 0x0   | Receive Overflow Mask                
 *  [8]     | RW     | 0x0   | Transmit FIFO Threshold Compare Mask 
 *  [9]     | RW     | 0x0   | Transmit FIFO Full Mask              
 *  [10]    | RW     | 0x0   | Receive FIFO Threshold Compare Mask  
 *  [11]    | RW     | 0x0   | Receive FIFO full Mask               
 *  [12]    | RW     | 0x0   | Indirect Read Partition overflow mask
 *  [31:13] | ???    | 0x0   | *UNDEFINED*                          
 * 
 */
/*
 * Field : Underflow Detected Mask - underflowdet
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                 
 * :------------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQMSK_UNDERFLOWDET_E_DISD | 0x0   | Disable Interrupt by Masking
 *  ALT_QSPI_IRQMSK_UNDERFLOWDET_E_END  | 0x1   | Enable Interrupt            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_UNDERFLOWDET
 * 
 * Disable Interrupt by Masking
 */
#define ALT_QSPI_IRQMSK_UNDERFLOWDET_E_DISD 0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_UNDERFLOWDET
 * 
 * Enable Interrupt
 */
#define ALT_QSPI_IRQMSK_UNDERFLOWDET_E_END  0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQMSK_UNDERFLOWDET register field. */
#define ALT_QSPI_IRQMSK_UNDERFLOWDET_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQMSK_UNDERFLOWDET register field. */
#define ALT_QSPI_IRQMSK_UNDERFLOWDET_MSB        1
/* The width in bits of the ALT_QSPI_IRQMSK_UNDERFLOWDET register field. */
#define ALT_QSPI_IRQMSK_UNDERFLOWDET_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQMSK_UNDERFLOWDET register field value. */
#define ALT_QSPI_IRQMSK_UNDERFLOWDET_SET_MSK    0x00000002
/* The mask used to clear the ALT_QSPI_IRQMSK_UNDERFLOWDET register field value. */
#define ALT_QSPI_IRQMSK_UNDERFLOWDET_CLR_MSK    0xfffffffd
/* The reset value of the ALT_QSPI_IRQMSK_UNDERFLOWDET register field. */
#define ALT_QSPI_IRQMSK_UNDERFLOWDET_RESET      0x0
/* Extracts the ALT_QSPI_IRQMSK_UNDERFLOWDET field value from a register. */
#define ALT_QSPI_IRQMSK_UNDERFLOWDET_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_QSPI_IRQMSK_UNDERFLOWDET register field value suitable for setting the register. */
#define ALT_QSPI_IRQMSK_UNDERFLOWDET_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Mask - indopdone
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                 
 * :---------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQMSK_INDOPDONE_E_DISD | 0x0   | Disable Interrupt by Masking
 *  ALT_QSPI_IRQMSK_INDOPDONE_E_END  | 0x1   | Enable Interrupt            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_INDOPDONE
 * 
 * Disable Interrupt by Masking
 */
#define ALT_QSPI_IRQMSK_INDOPDONE_E_DISD    0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_INDOPDONE
 * 
 * Enable Interrupt
 */
#define ALT_QSPI_IRQMSK_INDOPDONE_E_END     0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQMSK_INDOPDONE register field. */
#define ALT_QSPI_IRQMSK_INDOPDONE_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQMSK_INDOPDONE register field. */
#define ALT_QSPI_IRQMSK_INDOPDONE_MSB        2
/* The width in bits of the ALT_QSPI_IRQMSK_INDOPDONE register field. */
#define ALT_QSPI_IRQMSK_INDOPDONE_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQMSK_INDOPDONE register field value. */
#define ALT_QSPI_IRQMSK_INDOPDONE_SET_MSK    0x00000004
/* The mask used to clear the ALT_QSPI_IRQMSK_INDOPDONE register field value. */
#define ALT_QSPI_IRQMSK_INDOPDONE_CLR_MSK    0xfffffffb
/* The reset value of the ALT_QSPI_IRQMSK_INDOPDONE register field. */
#define ALT_QSPI_IRQMSK_INDOPDONE_RESET      0x0
/* Extracts the ALT_QSPI_IRQMSK_INDOPDONE field value from a register. */
#define ALT_QSPI_IRQMSK_INDOPDONE_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_QSPI_IRQMSK_INDOPDONE register field value suitable for setting the register. */
#define ALT_QSPI_IRQMSK_INDOPDONE_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Indirect Read Reject Mask - indrdreject
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                 
 * :-----------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQMSK_INDRDREJECT_E_DISD | 0x0   | Disable Interrupt by Masking
 *  ALT_QSPI_IRQMSK_INDRDREJECT_E_END  | 0x1   | Enable Interrupt            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_INDRDREJECT
 * 
 * Disable Interrupt by Masking
 */
#define ALT_QSPI_IRQMSK_INDRDREJECT_E_DISD  0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_INDRDREJECT
 * 
 * Enable Interrupt
 */
#define ALT_QSPI_IRQMSK_INDRDREJECT_E_END   0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQMSK_INDRDREJECT register field. */
#define ALT_QSPI_IRQMSK_INDRDREJECT_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQMSK_INDRDREJECT register field. */
#define ALT_QSPI_IRQMSK_INDRDREJECT_MSB        3
/* The width in bits of the ALT_QSPI_IRQMSK_INDRDREJECT register field. */
#define ALT_QSPI_IRQMSK_INDRDREJECT_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQMSK_INDRDREJECT register field value. */
#define ALT_QSPI_IRQMSK_INDRDREJECT_SET_MSK    0x00000008
/* The mask used to clear the ALT_QSPI_IRQMSK_INDRDREJECT register field value. */
#define ALT_QSPI_IRQMSK_INDRDREJECT_CLR_MSK    0xfffffff7
/* The reset value of the ALT_QSPI_IRQMSK_INDRDREJECT register field. */
#define ALT_QSPI_IRQMSK_INDRDREJECT_RESET      0x0
/* Extracts the ALT_QSPI_IRQMSK_INDRDREJECT field value from a register. */
#define ALT_QSPI_IRQMSK_INDRDREJECT_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_QSPI_IRQMSK_INDRDREJECT register field value suitable for setting the register. */
#define ALT_QSPI_IRQMSK_INDRDREJECT_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Protected Area Write Attempt Mask - protwrattempt
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description                 
 * :-------------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQMSK_PROTWRATTEMPT_E_DISD | 0x0   | Disable Interrupt by Masking
 *  ALT_QSPI_IRQMSK_PROTWRATTEMPT_E_END  | 0x1   | Enable Interrupt            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_PROTWRATTEMPT
 * 
 * Disable Interrupt by Masking
 */
#define ALT_QSPI_IRQMSK_PROTWRATTEMPT_E_DISD    0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_PROTWRATTEMPT
 * 
 * Enable Interrupt
 */
#define ALT_QSPI_IRQMSK_PROTWRATTEMPT_E_END     0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQMSK_PROTWRATTEMPT register field. */
#define ALT_QSPI_IRQMSK_PROTWRATTEMPT_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQMSK_PROTWRATTEMPT register field. */
#define ALT_QSPI_IRQMSK_PROTWRATTEMPT_MSB        4
/* The width in bits of the ALT_QSPI_IRQMSK_PROTWRATTEMPT register field. */
#define ALT_QSPI_IRQMSK_PROTWRATTEMPT_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQMSK_PROTWRATTEMPT register field value. */
#define ALT_QSPI_IRQMSK_PROTWRATTEMPT_SET_MSK    0x00000010
/* The mask used to clear the ALT_QSPI_IRQMSK_PROTWRATTEMPT register field value. */
#define ALT_QSPI_IRQMSK_PROTWRATTEMPT_CLR_MSK    0xffffffef
/* The reset value of the ALT_QSPI_IRQMSK_PROTWRATTEMPT register field. */
#define ALT_QSPI_IRQMSK_PROTWRATTEMPT_RESET      0x0
/* Extracts the ALT_QSPI_IRQMSK_PROTWRATTEMPT field value from a register. */
#define ALT_QSPI_IRQMSK_PROTWRATTEMPT_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_QSPI_IRQMSK_PROTWRATTEMPT register field value suitable for setting the register. */
#define ALT_QSPI_IRQMSK_PROTWRATTEMPT_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Illegal Access Detected Mask - illegalacc
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                 
 * :----------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQMSK_ILLEGALACC_E_DISD | 0x0   | Disable Interrupt by Masking
 *  ALT_QSPI_IRQMSK_ILLEGALACC_E_END  | 0x1   | Enable Interrupt            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_ILLEGALACC
 * 
 * Disable Interrupt by Masking
 */
#define ALT_QSPI_IRQMSK_ILLEGALACC_E_DISD   0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_ILLEGALACC
 * 
 * Enable Interrupt
 */
#define ALT_QSPI_IRQMSK_ILLEGALACC_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQMSK_ILLEGALACC register field. */
#define ALT_QSPI_IRQMSK_ILLEGALACC_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQMSK_ILLEGALACC register field. */
#define ALT_QSPI_IRQMSK_ILLEGALACC_MSB        5
/* The width in bits of the ALT_QSPI_IRQMSK_ILLEGALACC register field. */
#define ALT_QSPI_IRQMSK_ILLEGALACC_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQMSK_ILLEGALACC register field value. */
#define ALT_QSPI_IRQMSK_ILLEGALACC_SET_MSK    0x00000020
/* The mask used to clear the ALT_QSPI_IRQMSK_ILLEGALACC register field value. */
#define ALT_QSPI_IRQMSK_ILLEGALACC_CLR_MSK    0xffffffdf
/* The reset value of the ALT_QSPI_IRQMSK_ILLEGALACC register field. */
#define ALT_QSPI_IRQMSK_ILLEGALACC_RESET      0x0
/* Extracts the ALT_QSPI_IRQMSK_ILLEGALACC field value from a register. */
#define ALT_QSPI_IRQMSK_ILLEGALACC_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_QSPI_IRQMSK_ILLEGALACC register field value suitable for setting the register. */
#define ALT_QSPI_IRQMSK_ILLEGALACC_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Transfer Watermark Breach Mask - indxfrlvl
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                 
 * :---------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQMSK_INDXFRLVL_E_DISD | 0x0   | Disable Interrupt by Masking
 *  ALT_QSPI_IRQMSK_INDXFRLVL_E_END  | 0x1   | Enable Interrupt            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_INDXFRLVL
 * 
 * Disable Interrupt by Masking
 */
#define ALT_QSPI_IRQMSK_INDXFRLVL_E_DISD    0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_INDXFRLVL
 * 
 * Enable Interrupt
 */
#define ALT_QSPI_IRQMSK_INDXFRLVL_E_END     0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQMSK_INDXFRLVL register field. */
#define ALT_QSPI_IRQMSK_INDXFRLVL_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQMSK_INDXFRLVL register field. */
#define ALT_QSPI_IRQMSK_INDXFRLVL_MSB        6
/* The width in bits of the ALT_QSPI_IRQMSK_INDXFRLVL register field. */
#define ALT_QSPI_IRQMSK_INDXFRLVL_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQMSK_INDXFRLVL register field value. */
#define ALT_QSPI_IRQMSK_INDXFRLVL_SET_MSK    0x00000040
/* The mask used to clear the ALT_QSPI_IRQMSK_INDXFRLVL register field value. */
#define ALT_QSPI_IRQMSK_INDXFRLVL_CLR_MSK    0xffffffbf
/* The reset value of the ALT_QSPI_IRQMSK_INDXFRLVL register field. */
#define ALT_QSPI_IRQMSK_INDXFRLVL_RESET      0x0
/* Extracts the ALT_QSPI_IRQMSK_INDXFRLVL field value from a register. */
#define ALT_QSPI_IRQMSK_INDXFRLVL_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_QSPI_IRQMSK_INDXFRLVL register field value suitable for setting the register. */
#define ALT_QSPI_IRQMSK_INDXFRLVL_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Receive Overflow Mask - rxover
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                 
 * :------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQMSK_RXOVER_E_DISD | 0x0   | Disable Interrupt by Masking
 *  ALT_QSPI_IRQMSK_RXOVER_E_END  | 0x1   | Enable Interrupt            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_RXOVER
 * 
 * Disable Interrupt by Masking
 */
#define ALT_QSPI_IRQMSK_RXOVER_E_DISD   0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_RXOVER
 * 
 * Enable Interrupt
 */
#define ALT_QSPI_IRQMSK_RXOVER_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQMSK_RXOVER register field. */
#define ALT_QSPI_IRQMSK_RXOVER_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQMSK_RXOVER register field. */
#define ALT_QSPI_IRQMSK_RXOVER_MSB        7
/* The width in bits of the ALT_QSPI_IRQMSK_RXOVER register field. */
#define ALT_QSPI_IRQMSK_RXOVER_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQMSK_RXOVER register field value. */
#define ALT_QSPI_IRQMSK_RXOVER_SET_MSK    0x00000080
/* The mask used to clear the ALT_QSPI_IRQMSK_RXOVER register field value. */
#define ALT_QSPI_IRQMSK_RXOVER_CLR_MSK    0xffffff7f
/* The reset value of the ALT_QSPI_IRQMSK_RXOVER register field. */
#define ALT_QSPI_IRQMSK_RXOVER_RESET      0x0
/* Extracts the ALT_QSPI_IRQMSK_RXOVER field value from a register. */
#define ALT_QSPI_IRQMSK_RXOVER_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_QSPI_IRQMSK_RXOVER register field value suitable for setting the register. */
#define ALT_QSPI_IRQMSK_RXOVER_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Transmit FIFO Threshold Compare Mask - txthreshcmp
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                 
 * :-----------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQMSK_TXTHRESHCMP_E_DISD | 0x0   | Disable Interrupt by Masking
 *  ALT_QSPI_IRQMSK_TXTHRESHCMP_E_END  | 0x1   | Enable Interrupt            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_TXTHRESHCMP
 * 
 * Disable Interrupt by Masking
 */
#define ALT_QSPI_IRQMSK_TXTHRESHCMP_E_DISD  0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_TXTHRESHCMP
 * 
 * Enable Interrupt
 */
#define ALT_QSPI_IRQMSK_TXTHRESHCMP_E_END   0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQMSK_TXTHRESHCMP register field. */
#define ALT_QSPI_IRQMSK_TXTHRESHCMP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQMSK_TXTHRESHCMP register field. */
#define ALT_QSPI_IRQMSK_TXTHRESHCMP_MSB        8
/* The width in bits of the ALT_QSPI_IRQMSK_TXTHRESHCMP register field. */
#define ALT_QSPI_IRQMSK_TXTHRESHCMP_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQMSK_TXTHRESHCMP register field value. */
#define ALT_QSPI_IRQMSK_TXTHRESHCMP_SET_MSK    0x00000100
/* The mask used to clear the ALT_QSPI_IRQMSK_TXTHRESHCMP register field value. */
#define ALT_QSPI_IRQMSK_TXTHRESHCMP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_QSPI_IRQMSK_TXTHRESHCMP register field. */
#define ALT_QSPI_IRQMSK_TXTHRESHCMP_RESET      0x0
/* Extracts the ALT_QSPI_IRQMSK_TXTHRESHCMP field value from a register. */
#define ALT_QSPI_IRQMSK_TXTHRESHCMP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_QSPI_IRQMSK_TXTHRESHCMP register field value suitable for setting the register. */
#define ALT_QSPI_IRQMSK_TXTHRESHCMP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Transmit FIFO Full Mask - txfull
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                 
 * :------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQMSK_TXFULL_E_DISD | 0x0   | Disable Interrupt by Masking
 *  ALT_QSPI_IRQMSK_TXFULL_E_END  | 0x1   | Enable Interrupt            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_TXFULL
 * 
 * Disable Interrupt by Masking
 */
#define ALT_QSPI_IRQMSK_TXFULL_E_DISD   0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_TXFULL
 * 
 * Enable Interrupt
 */
#define ALT_QSPI_IRQMSK_TXFULL_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQMSK_TXFULL register field. */
#define ALT_QSPI_IRQMSK_TXFULL_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQMSK_TXFULL register field. */
#define ALT_QSPI_IRQMSK_TXFULL_MSB        9
/* The width in bits of the ALT_QSPI_IRQMSK_TXFULL register field. */
#define ALT_QSPI_IRQMSK_TXFULL_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQMSK_TXFULL register field value. */
#define ALT_QSPI_IRQMSK_TXFULL_SET_MSK    0x00000200
/* The mask used to clear the ALT_QSPI_IRQMSK_TXFULL register field value. */
#define ALT_QSPI_IRQMSK_TXFULL_CLR_MSK    0xfffffdff
/* The reset value of the ALT_QSPI_IRQMSK_TXFULL register field. */
#define ALT_QSPI_IRQMSK_TXFULL_RESET      0x0
/* Extracts the ALT_QSPI_IRQMSK_TXFULL field value from a register. */
#define ALT_QSPI_IRQMSK_TXFULL_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_QSPI_IRQMSK_TXFULL register field value suitable for setting the register. */
#define ALT_QSPI_IRQMSK_TXFULL_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Receive FIFO Threshold Compare Mask - rxthreshcmp
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                 
 * :-----------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQMSK_RXTHRESHCMP_E_DISD | 0x0   | Disable Interrupt by Masking
 *  ALT_QSPI_IRQMSK_RXTHRESHCMP_E_END  | 0x1   | Enable Interrupt            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_RXTHRESHCMP
 * 
 * Disable Interrupt by Masking
 */
#define ALT_QSPI_IRQMSK_RXTHRESHCMP_E_DISD  0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_RXTHRESHCMP
 * 
 * Enable Interrupt
 */
#define ALT_QSPI_IRQMSK_RXTHRESHCMP_E_END   0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQMSK_RXTHRESHCMP register field. */
#define ALT_QSPI_IRQMSK_RXTHRESHCMP_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQMSK_RXTHRESHCMP register field. */
#define ALT_QSPI_IRQMSK_RXTHRESHCMP_MSB        10
/* The width in bits of the ALT_QSPI_IRQMSK_RXTHRESHCMP register field. */
#define ALT_QSPI_IRQMSK_RXTHRESHCMP_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQMSK_RXTHRESHCMP register field value. */
#define ALT_QSPI_IRQMSK_RXTHRESHCMP_SET_MSK    0x00000400
/* The mask used to clear the ALT_QSPI_IRQMSK_RXTHRESHCMP register field value. */
#define ALT_QSPI_IRQMSK_RXTHRESHCMP_CLR_MSK    0xfffffbff
/* The reset value of the ALT_QSPI_IRQMSK_RXTHRESHCMP register field. */
#define ALT_QSPI_IRQMSK_RXTHRESHCMP_RESET      0x0
/* Extracts the ALT_QSPI_IRQMSK_RXTHRESHCMP field value from a register. */
#define ALT_QSPI_IRQMSK_RXTHRESHCMP_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_QSPI_IRQMSK_RXTHRESHCMP register field value suitable for setting the register. */
#define ALT_QSPI_IRQMSK_RXTHRESHCMP_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Receive FIFO full Mask - rxfull
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                 
 * :------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQMSK_RXFULL_E_DISD | 0x0   | Disable Interrupt by Masking
 *  ALT_QSPI_IRQMSK_RXFULL_E_END  | 0x1   | Enable Interrupt            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_RXFULL
 * 
 * Disable Interrupt by Masking
 */
#define ALT_QSPI_IRQMSK_RXFULL_E_DISD   0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_RXFULL
 * 
 * Enable Interrupt
 */
#define ALT_QSPI_IRQMSK_RXFULL_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQMSK_RXFULL register field. */
#define ALT_QSPI_IRQMSK_RXFULL_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQMSK_RXFULL register field. */
#define ALT_QSPI_IRQMSK_RXFULL_MSB        11
/* The width in bits of the ALT_QSPI_IRQMSK_RXFULL register field. */
#define ALT_QSPI_IRQMSK_RXFULL_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQMSK_RXFULL register field value. */
#define ALT_QSPI_IRQMSK_RXFULL_SET_MSK    0x00000800
/* The mask used to clear the ALT_QSPI_IRQMSK_RXFULL register field value. */
#define ALT_QSPI_IRQMSK_RXFULL_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_QSPI_IRQMSK_RXFULL register field. */
#define ALT_QSPI_IRQMSK_RXFULL_RESET      0x0
/* Extracts the ALT_QSPI_IRQMSK_RXFULL field value from a register. */
#define ALT_QSPI_IRQMSK_RXFULL_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_QSPI_IRQMSK_RXFULL register field value suitable for setting the register. */
#define ALT_QSPI_IRQMSK_RXFULL_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : Indirect Read Partition overflow mask - indsramfull
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                 
 * :-----------------------------------|:------|:-----------------------------
 *  ALT_QSPI_IRQMSK_INDSRAMFULL_E_DISD | 0x0   | Disable Interrupt by Masking
 *  ALT_QSPI_IRQMSK_INDSRAMFULL_E_END  | 0x1   | Enable Interrupt            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_INDSRAMFULL
 * 
 * Disable Interrupt by Masking
 */
#define ALT_QSPI_IRQMSK_INDSRAMFULL_E_DISD  0x0
/*
 * Enumerated value for register field ALT_QSPI_IRQMSK_INDSRAMFULL
 * 
 * Enable Interrupt
 */
#define ALT_QSPI_IRQMSK_INDSRAMFULL_E_END   0x1

/* The Least Significant Bit (LSB) position of the ALT_QSPI_IRQMSK_INDSRAMFULL register field. */
#define ALT_QSPI_IRQMSK_INDSRAMFULL_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_QSPI_IRQMSK_INDSRAMFULL register field. */
#define ALT_QSPI_IRQMSK_INDSRAMFULL_MSB        12
/* The width in bits of the ALT_QSPI_IRQMSK_INDSRAMFULL register field. */
#define ALT_QSPI_IRQMSK_INDSRAMFULL_WIDTH      1
/* The mask used to set the ALT_QSPI_IRQMSK_INDSRAMFULL register field value. */
#define ALT_QSPI_IRQMSK_INDSRAMFULL_SET_MSK    0x00001000
/* The mask used to clear the ALT_QSPI_IRQMSK_INDSRAMFULL register field value. */
#define ALT_QSPI_IRQMSK_INDSRAMFULL_CLR_MSK    0xffffefff
/* The reset value of the ALT_QSPI_IRQMSK_INDSRAMFULL register field. */
#define ALT_QSPI_IRQMSK_INDSRAMFULL_RESET      0x0
/* Extracts the ALT_QSPI_IRQMSK_INDSRAMFULL field value from a register. */
#define ALT_QSPI_IRQMSK_INDSRAMFULL_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_QSPI_IRQMSK_INDSRAMFULL register field value suitable for setting the register. */
#define ALT_QSPI_IRQMSK_INDSRAMFULL_SET(value) (((value) << 12) & 0x00001000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_IRQMSK.
 */
struct ALT_QSPI_IRQMSK_s
{
    uint32_t                :  1;  /* *UNDEFINED* */
    uint32_t  underflowdet  :  1;  /* Underflow Detected Mask */
    uint32_t  indopdone     :  1;  /* Mask */
    uint32_t  indrdreject   :  1;  /* Indirect Read Reject Mask */
    uint32_t  protwrattempt :  1;  /* Protected Area Write Attempt Mask */
    uint32_t  illegalacc    :  1;  /* Illegal Access Detected Mask */
    uint32_t  indxfrlvl     :  1;  /* Transfer Watermark Breach Mask */
    uint32_t  rxover        :  1;  /* Receive Overflow Mask */
    uint32_t  txthreshcmp   :  1;  /* Transmit FIFO Threshold Compare Mask */
    uint32_t  txfull        :  1;  /* Transmit FIFO Full Mask */
    uint32_t  rxthreshcmp   :  1;  /* Receive FIFO Threshold Compare Mask */
    uint32_t  rxfull        :  1;  /* Receive FIFO full Mask */
    uint32_t  indsramfull   :  1;  /* Indirect Read Partition overflow mask */
    uint32_t                : 19;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_IRQMSK. */
typedef volatile struct ALT_QSPI_IRQMSK_s  ALT_QSPI_IRQMSK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_IRQMSK register from the beginning of the component. */
#define ALT_QSPI_IRQMSK_OFST        0x44

/*
 * Register : Lower Write Protection Register - lowwrprot
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description 
 * :-------|:-------|:------|:-------------
 *  [31:0] | RW     | 0x0   | Block Number
 * 
 */
/*
 * Field : Block Number - subsector
 * 
 * The block number that defines the lower block in the range of blocks that is to
 * be locked from writing. The definition of a block in terms of number of bytes is
 * programmable via the Device Size Configuration register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_LOWWRPROT_SUBSECTOR register field. */
#define ALT_QSPI_LOWWRPROT_SUBSECTOR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_LOWWRPROT_SUBSECTOR register field. */
#define ALT_QSPI_LOWWRPROT_SUBSECTOR_MSB        31
/* The width in bits of the ALT_QSPI_LOWWRPROT_SUBSECTOR register field. */
#define ALT_QSPI_LOWWRPROT_SUBSECTOR_WIDTH      32
/* The mask used to set the ALT_QSPI_LOWWRPROT_SUBSECTOR register field value. */
#define ALT_QSPI_LOWWRPROT_SUBSECTOR_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_LOWWRPROT_SUBSECTOR register field value. */
#define ALT_QSPI_LOWWRPROT_SUBSECTOR_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_LOWWRPROT_SUBSECTOR register field. */
#define ALT_QSPI_LOWWRPROT_SUBSECTOR_RESET      0x0
/* Extracts the ALT_QSPI_LOWWRPROT_SUBSECTOR field value from a register. */
#define ALT_QSPI_LOWWRPROT_SUBSECTOR_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_LOWWRPROT_SUBSECTOR register field value suitable for setting the register. */
#define ALT_QSPI_LOWWRPROT_SUBSECTOR_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_LOWWRPROT.
 */
struct ALT_QSPI_LOWWRPROT_s
{
    uint32_t  subsector : 32;  /* Block Number */
};

/* The typedef declaration for register ALT_QSPI_LOWWRPROT. */
typedef volatile struct ALT_QSPI_LOWWRPROT_s  ALT_QSPI_LOWWRPROT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_LOWWRPROT register from the beginning of the component. */
#define ALT_QSPI_LOWWRPROT_OFST        0x50

/*
 * Register : Upper Write Protection Register - uppwrprot
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description 
 * :-------|:-------|:------|:-------------
 *  [31:0] | RW     | 0x0   | Block Number
 * 
 */
/*
 * Field : Block Number - subsector
 * 
 * The block number that defines the upper block in the range of blocks that is to
 * be locked from writing. The definition of a block in terms of number of bytes is
 * programmable via the Device Size Configuration register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_UPPWRPROT_SUBSECTOR register field. */
#define ALT_QSPI_UPPWRPROT_SUBSECTOR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_UPPWRPROT_SUBSECTOR register field. */
#define ALT_QSPI_UPPWRPROT_SUBSECTOR_MSB        31
/* The width in bits of the ALT_QSPI_UPPWRPROT_SUBSECTOR register field. */
#define ALT_QSPI_UPPWRPROT_SUBSECTOR_WIDTH      32
/* The mask used to set the ALT_QSPI_UPPWRPROT_SUBSECTOR register field value. */
#define ALT_QSPI_UPPWRPROT_SUBSECTOR_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_UPPWRPROT_SUBSECTOR register field value. */
#define ALT_QSPI_UPPWRPROT_SUBSECTOR_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_UPPWRPROT_SUBSECTOR register field. */
#define ALT_QSPI_UPPWRPROT_SUBSECTOR_RESET      0x0
/* Extracts the ALT_QSPI_UPPWRPROT_SUBSECTOR field value from a register. */
#define ALT_QSPI_UPPWRPROT_SUBSECTOR_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_UPPWRPROT_SUBSECTOR register field value suitable for setting the register. */
#define ALT_QSPI_UPPWRPROT_SUBSECTOR_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_UPPWRPROT.
 */
struct ALT_QSPI_UPPWRPROT_s
{
    uint32_t  subsector : 32;  /* Block Number */
};

/* The typedef declaration for register ALT_QSPI_UPPWRPROT. */
typedef volatile struct ALT_QSPI_UPPWRPROT_s  ALT_QSPI_UPPWRPROT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_UPPWRPROT register from the beginning of the component. */
#define ALT_QSPI_UPPWRPROT_OFST        0x54

/*
 * Register : Write Protection Register - wrprot
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                   
 * :-------|:-------|:------|:-------------------------------
 *  [0]    | RW     | 0x0   | Write Protection Inversion Bit
 *  [1]    | RW     | 0x0   | Write Protection Enable Bit   
 *  [31:2] | ???    | 0x0   | *UNDEFINED*                   
 * 
 */
/*
 * Field : Write Protection Inversion Bit - inv
 * 
 * When enabled, the protection region defined in the lower and upper write
 * protection registers is inverted meaning it is the region that the system is
 * permitted to write to. When disabled, the protection region defined in the lower
 * and upper write protection registers is the region that the system is not
 * permitted to write to.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description             
 * :--------------------------|:------|:-------------------------
 *  ALT_QSPI_WRPROT_INV_E_EN  | 0x1   | Write Region allowed    
 *  ALT_QSPI_WRPROT_INV_E_DIS | 0x0   | Write Region not allowed
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_WRPROT_INV
 * 
 * Write Region allowed
 */
#define ALT_QSPI_WRPROT_INV_E_EN    0x1
/*
 * Enumerated value for register field ALT_QSPI_WRPROT_INV
 * 
 * Write Region not allowed
 */
#define ALT_QSPI_WRPROT_INV_E_DIS   0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_WRPROT_INV register field. */
#define ALT_QSPI_WRPROT_INV_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_WRPROT_INV register field. */
#define ALT_QSPI_WRPROT_INV_MSB        0
/* The width in bits of the ALT_QSPI_WRPROT_INV register field. */
#define ALT_QSPI_WRPROT_INV_WIDTH      1
/* The mask used to set the ALT_QSPI_WRPROT_INV register field value. */
#define ALT_QSPI_WRPROT_INV_SET_MSK    0x00000001
/* The mask used to clear the ALT_QSPI_WRPROT_INV register field value. */
#define ALT_QSPI_WRPROT_INV_CLR_MSK    0xfffffffe
/* The reset value of the ALT_QSPI_WRPROT_INV register field. */
#define ALT_QSPI_WRPROT_INV_RESET      0x0
/* Extracts the ALT_QSPI_WRPROT_INV field value from a register. */
#define ALT_QSPI_WRPROT_INV_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_QSPI_WRPROT_INV register field value suitable for setting the register. */
#define ALT_QSPI_WRPROT_INV_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Write Protection Enable Bit - en
 * 
 * When enabled, any AHB write access with an address within the protection region
 * defined in the lower and upper write protection registers is rejected. An AHB
 * error response is generated and an interrupt source triggered. When disabled,
 * the protection region is disabled.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                     | Value | Description               
 * :-------------------------|:------|:---------------------------
 *  ALT_QSPI_WRPROT_EN_E_EN  | 0x1   | AHB Write Access rejected 
 *  ALT_QSPI_WRPROT_EN_E_DIS | 0x0   | Protection Region Disabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_WRPROT_EN
 * 
 * AHB Write Access rejected
 */
#define ALT_QSPI_WRPROT_EN_E_EN     0x1
/*
 * Enumerated value for register field ALT_QSPI_WRPROT_EN
 * 
 * Protection Region Disabled
 */
#define ALT_QSPI_WRPROT_EN_E_DIS    0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_WRPROT_EN register field. */
#define ALT_QSPI_WRPROT_EN_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_QSPI_WRPROT_EN register field. */
#define ALT_QSPI_WRPROT_EN_MSB        1
/* The width in bits of the ALT_QSPI_WRPROT_EN register field. */
#define ALT_QSPI_WRPROT_EN_WIDTH      1
/* The mask used to set the ALT_QSPI_WRPROT_EN register field value. */
#define ALT_QSPI_WRPROT_EN_SET_MSK    0x00000002
/* The mask used to clear the ALT_QSPI_WRPROT_EN register field value. */
#define ALT_QSPI_WRPROT_EN_CLR_MSK    0xfffffffd
/* The reset value of the ALT_QSPI_WRPROT_EN register field. */
#define ALT_QSPI_WRPROT_EN_RESET      0x0
/* Extracts the ALT_QSPI_WRPROT_EN field value from a register. */
#define ALT_QSPI_WRPROT_EN_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_QSPI_WRPROT_EN register field value suitable for setting the register. */
#define ALT_QSPI_WRPROT_EN_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_WRPROT.
 */
struct ALT_QSPI_WRPROT_s
{
    uint32_t  inv :  1;  /* Write Protection Inversion Bit */
    uint32_t  en  :  1;  /* Write Protection Enable Bit */
    uint32_t      : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_WRPROT. */
typedef volatile struct ALT_QSPI_WRPROT_s  ALT_QSPI_WRPROT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_WRPROT register from the beginning of the component. */
#define ALT_QSPI_WRPROT_OFST        0x58

/*
 * Register : Indirect Read Transfer Register - indrd
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description                    
 * :-------|:-------|:--------|:--------------------------------
 *  [0]    | RW     | 0x0     | Start Indirect Read            
 *  [1]    | RW     | 0x0     | Cancel Indirect Read           
 *  [2]    | R      | Unknown | Indirect Read Status           
 *  [3]    | RW     | Unknown | SRAM Full                      
 *  [4]    | R      | Unknown | Queued Indirect Read Operations
 *  [5]    | RW     | Unknown | Indirect Completion Status     
 *  [7:6]  | R      | Unknown | Completed Indirect Operations  
 *  [31:8] | ???    | 0x0     | *UNDEFINED*                    
 * 
 */
/*
 * Field : Start Indirect Read - start
 * 
 * When this bit is enabled, it will trigger an indirect read operation. The
 * assumption is that the indirect start address and the indirect number of bytes
 * register is setup before triggering the indirect read operation.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description          
 * :----------------------------|:------|:----------------------
 *  ALT_QSPI_INDRD_START_E_END  | 0x1   | Trigger Indirect Read
 *  ALT_QSPI_INDRD_START_E_DISD | 0x0   | No Indirect Read     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_INDRD_START
 * 
 * Trigger Indirect Read
 */
#define ALT_QSPI_INDRD_START_E_END  0x1
/*
 * Enumerated value for register field ALT_QSPI_INDRD_START
 * 
 * No Indirect Read
 */
#define ALT_QSPI_INDRD_START_E_DISD 0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDRD_START register field. */
#define ALT_QSPI_INDRD_START_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDRD_START register field. */
#define ALT_QSPI_INDRD_START_MSB        0
/* The width in bits of the ALT_QSPI_INDRD_START register field. */
#define ALT_QSPI_INDRD_START_WIDTH      1
/* The mask used to set the ALT_QSPI_INDRD_START register field value. */
#define ALT_QSPI_INDRD_START_SET_MSK    0x00000001
/* The mask used to clear the ALT_QSPI_INDRD_START register field value. */
#define ALT_QSPI_INDRD_START_CLR_MSK    0xfffffffe
/* The reset value of the ALT_QSPI_INDRD_START register field. */
#define ALT_QSPI_INDRD_START_RESET      0x0
/* Extracts the ALT_QSPI_INDRD_START field value from a register. */
#define ALT_QSPI_INDRD_START_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_QSPI_INDRD_START register field value suitable for setting the register. */
#define ALT_QSPI_INDRD_START_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Cancel Indirect Read - cancel
 * 
 * This bit will cancel all ongoing indirect read operations.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                
 * :---------------------------------|:------|:----------------------------
 *  ALT_QSPI_INDRD_CANCEL_E_CANCEL   | 0x1   | Cancel Indirect Read       
 *  ALT_QSPI_INDRD_CANCEL_E_NOACTION | 0x0   | Do Not Cancel Indirect Read
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_INDRD_CANCEL
 * 
 * Cancel Indirect Read
 */
#define ALT_QSPI_INDRD_CANCEL_E_CANCEL      0x1
/*
 * Enumerated value for register field ALT_QSPI_INDRD_CANCEL
 * 
 * Do Not Cancel Indirect Read
 */
#define ALT_QSPI_INDRD_CANCEL_E_NOACTION    0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDRD_CANCEL register field. */
#define ALT_QSPI_INDRD_CANCEL_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDRD_CANCEL register field. */
#define ALT_QSPI_INDRD_CANCEL_MSB        1
/* The width in bits of the ALT_QSPI_INDRD_CANCEL register field. */
#define ALT_QSPI_INDRD_CANCEL_WIDTH      1
/* The mask used to set the ALT_QSPI_INDRD_CANCEL register field value. */
#define ALT_QSPI_INDRD_CANCEL_SET_MSK    0x00000002
/* The mask used to clear the ALT_QSPI_INDRD_CANCEL register field value. */
#define ALT_QSPI_INDRD_CANCEL_CLR_MSK    0xfffffffd
/* The reset value of the ALT_QSPI_INDRD_CANCEL register field. */
#define ALT_QSPI_INDRD_CANCEL_RESET      0x0
/* Extracts the ALT_QSPI_INDRD_CANCEL field value from a register. */
#define ALT_QSPI_INDRD_CANCEL_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_QSPI_INDRD_CANCEL register field value suitable for setting the register. */
#define ALT_QSPI_INDRD_CANCEL_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Indirect Read Status - rd_status
 * 
 * Indirect read operation in progress (status)
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                  
 * :----------------------------------|:------|:------------------------------
 *  ALT_QSPI_INDRD_RD_STAT_E_RDOP     | 0x1   | Read Operation in progress   
 *  ALT_QSPI_INDRD_RD_STAT_E_NOACTION | 0x0   | No read operation in progress
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_INDRD_RD_STAT
 * 
 * Read Operation in progress
 */
#define ALT_QSPI_INDRD_RD_STAT_E_RDOP       0x1
/*
 * Enumerated value for register field ALT_QSPI_INDRD_RD_STAT
 * 
 * No read operation in progress
 */
#define ALT_QSPI_INDRD_RD_STAT_E_NOACTION   0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDRD_RD_STAT register field. */
#define ALT_QSPI_INDRD_RD_STAT_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDRD_RD_STAT register field. */
#define ALT_QSPI_INDRD_RD_STAT_MSB        2
/* The width in bits of the ALT_QSPI_INDRD_RD_STAT register field. */
#define ALT_QSPI_INDRD_RD_STAT_WIDTH      1
/* The mask used to set the ALT_QSPI_INDRD_RD_STAT register field value. */
#define ALT_QSPI_INDRD_RD_STAT_SET_MSK    0x00000004
/* The mask used to clear the ALT_QSPI_INDRD_RD_STAT register field value. */
#define ALT_QSPI_INDRD_RD_STAT_CLR_MSK    0xfffffffb
/* The reset value of the ALT_QSPI_INDRD_RD_STAT register field is UNKNOWN. */
#define ALT_QSPI_INDRD_RD_STAT_RESET      0x0
/* Extracts the ALT_QSPI_INDRD_RD_STAT field value from a register. */
#define ALT_QSPI_INDRD_RD_STAT_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_QSPI_INDRD_RD_STAT register field value suitable for setting the register. */
#define ALT_QSPI_INDRD_RD_STAT_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : SRAM Full - sram_full
 * 
 * SRAM full and unable to immediately complete an indirect operation. Write a 1 to
 * this field to clear it. ; indirect operation (status)
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                       
 * :------------------------------------|:------|:-----------------------------------
 *  ALT_QSPI_INDRD_SRAM_FULL_E_SRAMFULL | 0x1   | Sram Full- Cant complete operation
 *  ALT_QSPI_INDRD_SRAM_FULL_E_NOACTION | 0x0   | SRram Not Full                    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_INDRD_SRAM_FULL
 * 
 * Sram Full- Cant complete operation
 */
#define ALT_QSPI_INDRD_SRAM_FULL_E_SRAMFULL 0x1
/*
 * Enumerated value for register field ALT_QSPI_INDRD_SRAM_FULL
 * 
 * SRram Not Full
 */
#define ALT_QSPI_INDRD_SRAM_FULL_E_NOACTION 0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDRD_SRAM_FULL register field. */
#define ALT_QSPI_INDRD_SRAM_FULL_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDRD_SRAM_FULL register field. */
#define ALT_QSPI_INDRD_SRAM_FULL_MSB        3
/* The width in bits of the ALT_QSPI_INDRD_SRAM_FULL register field. */
#define ALT_QSPI_INDRD_SRAM_FULL_WIDTH      1
/* The mask used to set the ALT_QSPI_INDRD_SRAM_FULL register field value. */
#define ALT_QSPI_INDRD_SRAM_FULL_SET_MSK    0x00000008
/* The mask used to clear the ALT_QSPI_INDRD_SRAM_FULL register field value. */
#define ALT_QSPI_INDRD_SRAM_FULL_CLR_MSK    0xfffffff7
/* The reset value of the ALT_QSPI_INDRD_SRAM_FULL register field is UNKNOWN. */
#define ALT_QSPI_INDRD_SRAM_FULL_RESET      0x0
/* Extracts the ALT_QSPI_INDRD_SRAM_FULL field value from a register. */
#define ALT_QSPI_INDRD_SRAM_FULL_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_QSPI_INDRD_SRAM_FULL register field value suitable for setting the register. */
#define ALT_QSPI_INDRD_SRAM_FULL_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Queued Indirect Read Operations - rd_queued
 * 
 * Two indirect read operations have been queued
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                    | Value | Description         
 * :----------------------------------------|:------|:---------------------
 *  ALT_QSPI_INDRD_RD_QUEUED_E_QUINDIRECTRD | 0x1   | Queued Indirect Read
 *  ALT_QSPI_INDRD_RD_QUEUED_E_NOACTION     | 0x0   | No Queued Read      
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_INDRD_RD_QUEUED
 * 
 * Queued Indirect Read
 */
#define ALT_QSPI_INDRD_RD_QUEUED_E_QUINDIRECTRD 0x1
/*
 * Enumerated value for register field ALT_QSPI_INDRD_RD_QUEUED
 * 
 * No Queued Read
 */
#define ALT_QSPI_INDRD_RD_QUEUED_E_NOACTION     0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDRD_RD_QUEUED register field. */
#define ALT_QSPI_INDRD_RD_QUEUED_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDRD_RD_QUEUED register field. */
#define ALT_QSPI_INDRD_RD_QUEUED_MSB        4
/* The width in bits of the ALT_QSPI_INDRD_RD_QUEUED register field. */
#define ALT_QSPI_INDRD_RD_QUEUED_WIDTH      1
/* The mask used to set the ALT_QSPI_INDRD_RD_QUEUED register field value. */
#define ALT_QSPI_INDRD_RD_QUEUED_SET_MSK    0x00000010
/* The mask used to clear the ALT_QSPI_INDRD_RD_QUEUED register field value. */
#define ALT_QSPI_INDRD_RD_QUEUED_CLR_MSK    0xffffffef
/* The reset value of the ALT_QSPI_INDRD_RD_QUEUED register field is UNKNOWN. */
#define ALT_QSPI_INDRD_RD_QUEUED_RESET      0x0
/* Extracts the ALT_QSPI_INDRD_RD_QUEUED field value from a register. */
#define ALT_QSPI_INDRD_RD_QUEUED_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_QSPI_INDRD_RD_QUEUED register field value suitable for setting the register. */
#define ALT_QSPI_INDRD_RD_QUEUED_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Indirect Completion Status - ind_ops_done_status
 * 
 * This field is set to 1 when an indirect operation has completed. Write a 1 to
 * this field to clear it.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                        | Value | Description                   
 * :--------------------------------------------|:------|:-------------------------------
 *  ALT_QSPI_INDRD_IND_OPS_DONE_STAT_E_INDCOMP  | 0x1   | Indirect Op Complete operation
 *  ALT_QSPI_INDRD_IND_OPS_DONE_STAT_E_NOACTION | 0x0   | Indirect Op Not Complete      
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_INDRD_IND_OPS_DONE_STAT
 * 
 * Indirect Op Complete operation
 */
#define ALT_QSPI_INDRD_IND_OPS_DONE_STAT_E_INDCOMP  0x1
/*
 * Enumerated value for register field ALT_QSPI_INDRD_IND_OPS_DONE_STAT
 * 
 * Indirect Op Not Complete
 */
#define ALT_QSPI_INDRD_IND_OPS_DONE_STAT_E_NOACTION 0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDRD_IND_OPS_DONE_STAT register field. */
#define ALT_QSPI_INDRD_IND_OPS_DONE_STAT_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDRD_IND_OPS_DONE_STAT register field. */
#define ALT_QSPI_INDRD_IND_OPS_DONE_STAT_MSB        5
/* The width in bits of the ALT_QSPI_INDRD_IND_OPS_DONE_STAT register field. */
#define ALT_QSPI_INDRD_IND_OPS_DONE_STAT_WIDTH      1
/* The mask used to set the ALT_QSPI_INDRD_IND_OPS_DONE_STAT register field value. */
#define ALT_QSPI_INDRD_IND_OPS_DONE_STAT_SET_MSK    0x00000020
/* The mask used to clear the ALT_QSPI_INDRD_IND_OPS_DONE_STAT register field value. */
#define ALT_QSPI_INDRD_IND_OPS_DONE_STAT_CLR_MSK    0xffffffdf
/* The reset value of the ALT_QSPI_INDRD_IND_OPS_DONE_STAT register field is UNKNOWN. */
#define ALT_QSPI_INDRD_IND_OPS_DONE_STAT_RESET      0x0
/* Extracts the ALT_QSPI_INDRD_IND_OPS_DONE_STAT field value from a register. */
#define ALT_QSPI_INDRD_IND_OPS_DONE_STAT_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_QSPI_INDRD_IND_OPS_DONE_STAT register field value suitable for setting the register. */
#define ALT_QSPI_INDRD_IND_OPS_DONE_STAT_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Completed Indirect Operations - num_ind_ops_done
 * 
 * This field contains the number of indirect operations which have been completed.
 * This is used in conjunction with the indirect completion status field (bit 5).
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDRD_NUM_IND_OPS_DONE register field. */
#define ALT_QSPI_INDRD_NUM_IND_OPS_DONE_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDRD_NUM_IND_OPS_DONE register field. */
#define ALT_QSPI_INDRD_NUM_IND_OPS_DONE_MSB        7
/* The width in bits of the ALT_QSPI_INDRD_NUM_IND_OPS_DONE register field. */
#define ALT_QSPI_INDRD_NUM_IND_OPS_DONE_WIDTH      2
/* The mask used to set the ALT_QSPI_INDRD_NUM_IND_OPS_DONE register field value. */
#define ALT_QSPI_INDRD_NUM_IND_OPS_DONE_SET_MSK    0x000000c0
/* The mask used to clear the ALT_QSPI_INDRD_NUM_IND_OPS_DONE register field value. */
#define ALT_QSPI_INDRD_NUM_IND_OPS_DONE_CLR_MSK    0xffffff3f
/* The reset value of the ALT_QSPI_INDRD_NUM_IND_OPS_DONE register field is UNKNOWN. */
#define ALT_QSPI_INDRD_NUM_IND_OPS_DONE_RESET      0x0
/* Extracts the ALT_QSPI_INDRD_NUM_IND_OPS_DONE field value from a register. */
#define ALT_QSPI_INDRD_NUM_IND_OPS_DONE_GET(value) (((value) & 0x000000c0) >> 6)
/* Produces a ALT_QSPI_INDRD_NUM_IND_OPS_DONE register field value suitable for setting the register. */
#define ALT_QSPI_INDRD_NUM_IND_OPS_DONE_SET(value) (((value) << 6) & 0x000000c0)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_INDRD.
 */
struct ALT_QSPI_INDRD_s
{
    uint32_t        start               :  1;  /* Start Indirect Read */
    uint32_t        cancel              :  1;  /* Cancel Indirect Read */
    const uint32_t  rd_status           :  1;  /* Indirect Read Status */
    uint32_t        sram_full           :  1;  /* SRAM Full */
    const uint32_t  rd_queued           :  1;  /* Queued Indirect Read Operations */
    uint32_t        ind_ops_done_status :  1;  /* Indirect Completion Status */
    const uint32_t  num_ind_ops_done    :  2;  /* Completed Indirect Operations */
    uint32_t                            : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_INDRD. */
typedef volatile struct ALT_QSPI_INDRD_s  ALT_QSPI_INDRD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_INDRD register from the beginning of the component. */
#define ALT_QSPI_INDRD_OFST        0x60

/*
 * Register : Indirect Read Transfer Watermark Register - indrdwater
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description    
 * :-------|:-------|:------|:----------------
 *  [31:0] | RW     | 0x0   | Watermark Value
 * 
 */
/*
 * Field : Watermark Value - level
 * 
 * This represents the minimum fill level of the SRAM before a DMA peripheral
 * access is permitted. When the SRAM fill level passes the watermark, an interrupt
 * is also generated. This field can be disabled by writing a value of all zeroes.
 * The units of this register are BYTES
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDRDWATER_LEVEL register field. */
#define ALT_QSPI_INDRDWATER_LEVEL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDRDWATER_LEVEL register field. */
#define ALT_QSPI_INDRDWATER_LEVEL_MSB        31
/* The width in bits of the ALT_QSPI_INDRDWATER_LEVEL register field. */
#define ALT_QSPI_INDRDWATER_LEVEL_WIDTH      32
/* The mask used to set the ALT_QSPI_INDRDWATER_LEVEL register field value. */
#define ALT_QSPI_INDRDWATER_LEVEL_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_INDRDWATER_LEVEL register field value. */
#define ALT_QSPI_INDRDWATER_LEVEL_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_INDRDWATER_LEVEL register field. */
#define ALT_QSPI_INDRDWATER_LEVEL_RESET      0x0
/* Extracts the ALT_QSPI_INDRDWATER_LEVEL field value from a register. */
#define ALT_QSPI_INDRDWATER_LEVEL_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_INDRDWATER_LEVEL register field value suitable for setting the register. */
#define ALT_QSPI_INDRDWATER_LEVEL_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_INDRDWATER.
 */
struct ALT_QSPI_INDRDWATER_s
{
    uint32_t  level : 32;  /* Watermark Value */
};

/* The typedef declaration for register ALT_QSPI_INDRDWATER. */
typedef volatile struct ALT_QSPI_INDRDWATER_s  ALT_QSPI_INDRDWATER_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_INDRDWATER register from the beginning of the component. */
#define ALT_QSPI_INDRDWATER_OFST        0x64

/*
 * Register : Indirect Read Transfer Start Address Register - indrdstaddr
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                     
 * :-------|:-------|:------|:---------------------------------
 *  [31:0] | RW     | 0x0   | Start Address of Indirect Access
 * 
 */
/*
 * Field : Start Address of Indirect Access - addr
 * 
 * This is the start address from which the indirect access will commence its READ
 * operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDRDSTADDR_ADDR register field. */
#define ALT_QSPI_INDRDSTADDR_ADDR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDRDSTADDR_ADDR register field. */
#define ALT_QSPI_INDRDSTADDR_ADDR_MSB        31
/* The width in bits of the ALT_QSPI_INDRDSTADDR_ADDR register field. */
#define ALT_QSPI_INDRDSTADDR_ADDR_WIDTH      32
/* The mask used to set the ALT_QSPI_INDRDSTADDR_ADDR register field value. */
#define ALT_QSPI_INDRDSTADDR_ADDR_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_INDRDSTADDR_ADDR register field value. */
#define ALT_QSPI_INDRDSTADDR_ADDR_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_INDRDSTADDR_ADDR register field. */
#define ALT_QSPI_INDRDSTADDR_ADDR_RESET      0x0
/* Extracts the ALT_QSPI_INDRDSTADDR_ADDR field value from a register. */
#define ALT_QSPI_INDRDSTADDR_ADDR_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_INDRDSTADDR_ADDR register field value suitable for setting the register. */
#define ALT_QSPI_INDRDSTADDR_ADDR_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_INDRDSTADDR.
 */
struct ALT_QSPI_INDRDSTADDR_s
{
    uint32_t  addr : 32;  /* Start Address of Indirect Access */
};

/* The typedef declaration for register ALT_QSPI_INDRDSTADDR. */
typedef volatile struct ALT_QSPI_INDRDSTADDR_s  ALT_QSPI_INDRDSTADDR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_INDRDSTADDR register from the beginning of the component. */
#define ALT_QSPI_INDRDSTADDR_OFST        0x68

/*
 * Register : Indirect Read Transfer Number Bytes Register - indrdcnt
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description   
 * :-------|:-------|:------|:---------------
 *  [31:0] | RW     | 0x0   | Indirect Count
 * 
 */
/*
 * Field : Indirect Count - value
 * 
 * This is the number of bytes that the indirect access will consume. This can be
 * bigger than the configured size of SRAM.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDRDCNT_VALUE register field. */
#define ALT_QSPI_INDRDCNT_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDRDCNT_VALUE register field. */
#define ALT_QSPI_INDRDCNT_VALUE_MSB        31
/* The width in bits of the ALT_QSPI_INDRDCNT_VALUE register field. */
#define ALT_QSPI_INDRDCNT_VALUE_WIDTH      32
/* The mask used to set the ALT_QSPI_INDRDCNT_VALUE register field value. */
#define ALT_QSPI_INDRDCNT_VALUE_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_INDRDCNT_VALUE register field value. */
#define ALT_QSPI_INDRDCNT_VALUE_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_INDRDCNT_VALUE register field. */
#define ALT_QSPI_INDRDCNT_VALUE_RESET      0x0
/* Extracts the ALT_QSPI_INDRDCNT_VALUE field value from a register. */
#define ALT_QSPI_INDRDCNT_VALUE_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_INDRDCNT_VALUE register field value suitable for setting the register. */
#define ALT_QSPI_INDRDCNT_VALUE_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_INDRDCNT.
 */
struct ALT_QSPI_INDRDCNT_s
{
    uint32_t  value : 32;  /* Indirect Count */
};

/* The typedef declaration for register ALT_QSPI_INDRDCNT. */
typedef volatile struct ALT_QSPI_INDRDCNT_s  ALT_QSPI_INDRDCNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_INDRDCNT register from the beginning of the component. */
#define ALT_QSPI_INDRDCNT_OFST        0x6c

/*
 * Register : Indirect Write Transfer Register - indwr
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description                     
 * :-------|:-------|:--------|:---------------------------------
 *  [0]    | RW     | 0x0     | Start Indirect Write            
 *  [1]    | RW     | 0x0     | Cancel Indirect Write           
 *  [2]    | R      | Unknown | Indirect Write Status           
 *  [3]    | R      | 0x0     | Reserved                        
 *  [4]    | R      | Unknown | Queued Indirect Write Operations
 *  [5]    | RW     | Unknown | Indirect Completion Status      
 *  [7:6]  | R      | Unknown | Completed Indirect Operations   
 *  [31:8] | ???    | 0x0     | *UNDEFINED*                     
 * 
 */
/*
 * Field : Start Indirect Write - start
 * 
 * Writing a 1 to this bit will trigger an indirect write operation. The assumption
 * is that the indirect start address and the indirect number of bytes register is
 * setup before triggering the indirect write operation.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                     
 * :----------------------------|:------|:---------------------------------
 *  ALT_QSPI_INDWR_START_E_END  | 0x1   | Trigger indirect write operation
 *  ALT_QSPI_INDWR_START_E_DISD | 0x0   | No Action                       
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_INDWR_START
 * 
 * Trigger indirect write operation
 */
#define ALT_QSPI_INDWR_START_E_END  0x1
/*
 * Enumerated value for register field ALT_QSPI_INDWR_START
 * 
 * No Action
 */
#define ALT_QSPI_INDWR_START_E_DISD 0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDWR_START register field. */
#define ALT_QSPI_INDWR_START_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDWR_START register field. */
#define ALT_QSPI_INDWR_START_MSB        0
/* The width in bits of the ALT_QSPI_INDWR_START register field. */
#define ALT_QSPI_INDWR_START_WIDTH      1
/* The mask used to set the ALT_QSPI_INDWR_START register field value. */
#define ALT_QSPI_INDWR_START_SET_MSK    0x00000001
/* The mask used to clear the ALT_QSPI_INDWR_START register field value. */
#define ALT_QSPI_INDWR_START_CLR_MSK    0xfffffffe
/* The reset value of the ALT_QSPI_INDWR_START register field. */
#define ALT_QSPI_INDWR_START_RESET      0x0
/* Extracts the ALT_QSPI_INDWR_START field value from a register. */
#define ALT_QSPI_INDWR_START_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_QSPI_INDWR_START register field value suitable for setting the register. */
#define ALT_QSPI_INDWR_START_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Cancel Indirect Write - cancel
 * 
 * Writing a 1 to this bit will cancel all ongoing indirect write operations.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                    
 * :-----------------------------------|:------|:--------------------------------
 *  ALT_QSPI_INDWR_CANCEL_E_CANCEINDWR | 0x1   | Cancel Indirect write operation
 *  ALT_QSPI_INDWR_CANCEL_E_NOACTION   | 0x0   | No Action                      
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_INDWR_CANCEL
 * 
 * Cancel Indirect write operation
 */
#define ALT_QSPI_INDWR_CANCEL_E_CANCEINDWR  0x1
/*
 * Enumerated value for register field ALT_QSPI_INDWR_CANCEL
 * 
 * No Action
 */
#define ALT_QSPI_INDWR_CANCEL_E_NOACTION    0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDWR_CANCEL register field. */
#define ALT_QSPI_INDWR_CANCEL_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDWR_CANCEL register field. */
#define ALT_QSPI_INDWR_CANCEL_MSB        1
/* The width in bits of the ALT_QSPI_INDWR_CANCEL register field. */
#define ALT_QSPI_INDWR_CANCEL_WIDTH      1
/* The mask used to set the ALT_QSPI_INDWR_CANCEL register field value. */
#define ALT_QSPI_INDWR_CANCEL_SET_MSK    0x00000002
/* The mask used to clear the ALT_QSPI_INDWR_CANCEL register field value. */
#define ALT_QSPI_INDWR_CANCEL_CLR_MSK    0xfffffffd
/* The reset value of the ALT_QSPI_INDWR_CANCEL register field. */
#define ALT_QSPI_INDWR_CANCEL_RESET      0x0
/* Extracts the ALT_QSPI_INDWR_CANCEL field value from a register. */
#define ALT_QSPI_INDWR_CANCEL_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_QSPI_INDWR_CANCEL register field value suitable for setting the register. */
#define ALT_QSPI_INDWR_CANCEL_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Indirect Write Status - rdstat
 * 
 * Indirect write operation in progress (status)
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description             
 * :----------------------------------|:------|:-------------------------
 *  ALT_QSPI_INDWR_RDSTAT_E_INDWRSTAT | 0x1   | Indirect write operation
 *  ALT_QSPI_INDWR_RDSTAT_E_NOACTION  | 0x0   | No Action               
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_INDWR_RDSTAT
 * 
 * Indirect write operation
 */
#define ALT_QSPI_INDWR_RDSTAT_E_INDWRSTAT   0x1
/*
 * Enumerated value for register field ALT_QSPI_INDWR_RDSTAT
 * 
 * No Action
 */
#define ALT_QSPI_INDWR_RDSTAT_E_NOACTION    0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDWR_RDSTAT register field. */
#define ALT_QSPI_INDWR_RDSTAT_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDWR_RDSTAT register field. */
#define ALT_QSPI_INDWR_RDSTAT_MSB        2
/* The width in bits of the ALT_QSPI_INDWR_RDSTAT register field. */
#define ALT_QSPI_INDWR_RDSTAT_WIDTH      1
/* The mask used to set the ALT_QSPI_INDWR_RDSTAT register field value. */
#define ALT_QSPI_INDWR_RDSTAT_SET_MSK    0x00000004
/* The mask used to clear the ALT_QSPI_INDWR_RDSTAT register field value. */
#define ALT_QSPI_INDWR_RDSTAT_CLR_MSK    0xfffffffb
/* The reset value of the ALT_QSPI_INDWR_RDSTAT register field is UNKNOWN. */
#define ALT_QSPI_INDWR_RDSTAT_RESET      0x0
/* Extracts the ALT_QSPI_INDWR_RDSTAT field value from a register. */
#define ALT_QSPI_INDWR_RDSTAT_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_QSPI_INDWR_RDSTAT register field value suitable for setting the register. */
#define ALT_QSPI_INDWR_RDSTAT_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Reserved - sramfull
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDWR_SRAMFULL register field. */
#define ALT_QSPI_INDWR_SRAMFULL_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDWR_SRAMFULL register field. */
#define ALT_QSPI_INDWR_SRAMFULL_MSB        3
/* The width in bits of the ALT_QSPI_INDWR_SRAMFULL register field. */
#define ALT_QSPI_INDWR_SRAMFULL_WIDTH      1
/* The mask used to set the ALT_QSPI_INDWR_SRAMFULL register field value. */
#define ALT_QSPI_INDWR_SRAMFULL_SET_MSK    0x00000008
/* The mask used to clear the ALT_QSPI_INDWR_SRAMFULL register field value. */
#define ALT_QSPI_INDWR_SRAMFULL_CLR_MSK    0xfffffff7
/* The reset value of the ALT_QSPI_INDWR_SRAMFULL register field. */
#define ALT_QSPI_INDWR_SRAMFULL_RESET      0x0
/* Extracts the ALT_QSPI_INDWR_SRAMFULL field value from a register. */
#define ALT_QSPI_INDWR_SRAMFULL_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_QSPI_INDWR_SRAMFULL register field value suitable for setting the register. */
#define ALT_QSPI_INDWR_SRAMFULL_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Queued Indirect Write Operations - rdqueued
 * 
 * Two indirect write operations have been queued
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                 
 * :-----------------------------------|:------|:-----------------------------
 *  ALT_QSPI_INDWR_RDQUEUED_E_INDWROP  | 0x1   | Two Indirect write operation
 *  ALT_QSPI_INDWR_RDQUEUED_E_NOACTION | 0x0   | No Action                   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_INDWR_RDQUEUED
 * 
 * Two Indirect write operation
 */
#define ALT_QSPI_INDWR_RDQUEUED_E_INDWROP   0x1
/*
 * Enumerated value for register field ALT_QSPI_INDWR_RDQUEUED
 * 
 * No Action
 */
#define ALT_QSPI_INDWR_RDQUEUED_E_NOACTION  0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDWR_RDQUEUED register field. */
#define ALT_QSPI_INDWR_RDQUEUED_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDWR_RDQUEUED register field. */
#define ALT_QSPI_INDWR_RDQUEUED_MSB        4
/* The width in bits of the ALT_QSPI_INDWR_RDQUEUED register field. */
#define ALT_QSPI_INDWR_RDQUEUED_WIDTH      1
/* The mask used to set the ALT_QSPI_INDWR_RDQUEUED register field value. */
#define ALT_QSPI_INDWR_RDQUEUED_SET_MSK    0x00000010
/* The mask used to clear the ALT_QSPI_INDWR_RDQUEUED register field value. */
#define ALT_QSPI_INDWR_RDQUEUED_CLR_MSK    0xffffffef
/* The reset value of the ALT_QSPI_INDWR_RDQUEUED register field is UNKNOWN. */
#define ALT_QSPI_INDWR_RDQUEUED_RESET      0x0
/* Extracts the ALT_QSPI_INDWR_RDQUEUED field value from a register. */
#define ALT_QSPI_INDWR_RDQUEUED_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_QSPI_INDWR_RDQUEUED register field value suitable for setting the register. */
#define ALT_QSPI_INDWR_RDQUEUED_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Indirect Completion Status - inddone
 * 
 * This field is set to 1 when an indirect operation has completed. Write a 1 to
 * this field to clear it.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                 
 * :-----------------------------------|:------|:-----------------------------
 *  ALT_QSPI_INDWR_INDDONE_E_INDCOMPST | 0x1   | Indirect operation completed
 *  ALT_QSPI_INDWR_INDDONE_E_NOACTION  | 0x0   | No Action                   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_INDWR_INDDONE
 * 
 * Indirect operation completed
 */
#define ALT_QSPI_INDWR_INDDONE_E_INDCOMPST  0x1
/*
 * Enumerated value for register field ALT_QSPI_INDWR_INDDONE
 * 
 * No Action
 */
#define ALT_QSPI_INDWR_INDDONE_E_NOACTION   0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDWR_INDDONE register field. */
#define ALT_QSPI_INDWR_INDDONE_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDWR_INDDONE register field. */
#define ALT_QSPI_INDWR_INDDONE_MSB        5
/* The width in bits of the ALT_QSPI_INDWR_INDDONE register field. */
#define ALT_QSPI_INDWR_INDDONE_WIDTH      1
/* The mask used to set the ALT_QSPI_INDWR_INDDONE register field value. */
#define ALT_QSPI_INDWR_INDDONE_SET_MSK    0x00000020
/* The mask used to clear the ALT_QSPI_INDWR_INDDONE register field value. */
#define ALT_QSPI_INDWR_INDDONE_CLR_MSK    0xffffffdf
/* The reset value of the ALT_QSPI_INDWR_INDDONE register field is UNKNOWN. */
#define ALT_QSPI_INDWR_INDDONE_RESET      0x0
/* Extracts the ALT_QSPI_INDWR_INDDONE field value from a register. */
#define ALT_QSPI_INDWR_INDDONE_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_QSPI_INDWR_INDDONE register field value suitable for setting the register. */
#define ALT_QSPI_INDWR_INDDONE_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Completed Indirect Operations - indcnt
 * 
 * This field contains the count of indirect operations which have been completed.
 * This is used in conjunction with the indirect completion status field (bit 5).
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDWR_INDCNT register field. */
#define ALT_QSPI_INDWR_INDCNT_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDWR_INDCNT register field. */
#define ALT_QSPI_INDWR_INDCNT_MSB        7
/* The width in bits of the ALT_QSPI_INDWR_INDCNT register field. */
#define ALT_QSPI_INDWR_INDCNT_WIDTH      2
/* The mask used to set the ALT_QSPI_INDWR_INDCNT register field value. */
#define ALT_QSPI_INDWR_INDCNT_SET_MSK    0x000000c0
/* The mask used to clear the ALT_QSPI_INDWR_INDCNT register field value. */
#define ALT_QSPI_INDWR_INDCNT_CLR_MSK    0xffffff3f
/* The reset value of the ALT_QSPI_INDWR_INDCNT register field is UNKNOWN. */
#define ALT_QSPI_INDWR_INDCNT_RESET      0x0
/* Extracts the ALT_QSPI_INDWR_INDCNT field value from a register. */
#define ALT_QSPI_INDWR_INDCNT_GET(value) (((value) & 0x000000c0) >> 6)
/* Produces a ALT_QSPI_INDWR_INDCNT register field value suitable for setting the register. */
#define ALT_QSPI_INDWR_INDCNT_SET(value) (((value) << 6) & 0x000000c0)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_INDWR.
 */
struct ALT_QSPI_INDWR_s
{
    uint32_t        start    :  1;  /* Start Indirect Write */
    uint32_t        cancel   :  1;  /* Cancel Indirect Write */
    const uint32_t  rdstat   :  1;  /* Indirect Write Status */
    const uint32_t  sramfull :  1;  /* Reserved */
    const uint32_t  rdqueued :  1;  /* Queued Indirect Write Operations */
    uint32_t        inddone  :  1;  /* Indirect Completion Status */
    const uint32_t  indcnt   :  2;  /* Completed Indirect Operations */
    uint32_t                 : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_INDWR. */
typedef volatile struct ALT_QSPI_INDWR_s  ALT_QSPI_INDWR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_INDWR register from the beginning of the component. */
#define ALT_QSPI_INDWR_OFST        0x70

/*
 * Register : Indirect Write Transfer Watermark Register - indwrwater
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset      | Description    
 * :-------|:-------|:-----------|:----------------
 *  [31:0] | RW     | 0xffffffff | Watermark Value
 * 
 */
/*
 * Field : Watermark Value - level
 * 
 * This represents the maximum fill level of the SRAM before a DMA peripheral
 * access is permitted. When the SRAM fill level falls below the watermark, an
 * interrupt is also generated. This field can be disabled by writing a value of
 * all ones. The units of this register are bytes.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDWRWATER_LEVEL register field. */
#define ALT_QSPI_INDWRWATER_LEVEL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDWRWATER_LEVEL register field. */
#define ALT_QSPI_INDWRWATER_LEVEL_MSB        31
/* The width in bits of the ALT_QSPI_INDWRWATER_LEVEL register field. */
#define ALT_QSPI_INDWRWATER_LEVEL_WIDTH      32
/* The mask used to set the ALT_QSPI_INDWRWATER_LEVEL register field value. */
#define ALT_QSPI_INDWRWATER_LEVEL_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_INDWRWATER_LEVEL register field value. */
#define ALT_QSPI_INDWRWATER_LEVEL_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_INDWRWATER_LEVEL register field. */
#define ALT_QSPI_INDWRWATER_LEVEL_RESET      0xffffffff
/* Extracts the ALT_QSPI_INDWRWATER_LEVEL field value from a register. */
#define ALT_QSPI_INDWRWATER_LEVEL_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_INDWRWATER_LEVEL register field value suitable for setting the register. */
#define ALT_QSPI_INDWRWATER_LEVEL_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_INDWRWATER.
 */
struct ALT_QSPI_INDWRWATER_s
{
    uint32_t  level : 32;  /* Watermark Value */
};

/* The typedef declaration for register ALT_QSPI_INDWRWATER. */
typedef volatile struct ALT_QSPI_INDWRWATER_s  ALT_QSPI_INDWRWATER_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_INDWRWATER register from the beginning of the component. */
#define ALT_QSPI_INDWRWATER_OFST        0x74

/*
 * Register : Indirect Write Transfer Start Address Register - indwrstaddr
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description             
 * :-------|:-------|:------|:-------------------------
 *  [31:0] | RW     | 0x0   | Start of Indirect Access
 * 
 */
/*
 * Field : Start of Indirect Access - addr
 * 
 * This is the start address from which the indirect access will commence its write
 * operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDWRSTADDR_ADDR register field. */
#define ALT_QSPI_INDWRSTADDR_ADDR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDWRSTADDR_ADDR register field. */
#define ALT_QSPI_INDWRSTADDR_ADDR_MSB        31
/* The width in bits of the ALT_QSPI_INDWRSTADDR_ADDR register field. */
#define ALT_QSPI_INDWRSTADDR_ADDR_WIDTH      32
/* The mask used to set the ALT_QSPI_INDWRSTADDR_ADDR register field value. */
#define ALT_QSPI_INDWRSTADDR_ADDR_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_INDWRSTADDR_ADDR register field value. */
#define ALT_QSPI_INDWRSTADDR_ADDR_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_INDWRSTADDR_ADDR register field. */
#define ALT_QSPI_INDWRSTADDR_ADDR_RESET      0x0
/* Extracts the ALT_QSPI_INDWRSTADDR_ADDR field value from a register. */
#define ALT_QSPI_INDWRSTADDR_ADDR_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_INDWRSTADDR_ADDR register field value suitable for setting the register. */
#define ALT_QSPI_INDWRSTADDR_ADDR_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_INDWRSTADDR.
 */
struct ALT_QSPI_INDWRSTADDR_s
{
    uint32_t  addr : 32;  /* Start of Indirect Access */
};

/* The typedef declaration for register ALT_QSPI_INDWRSTADDR. */
typedef volatile struct ALT_QSPI_INDWRSTADDR_s  ALT_QSPI_INDWRSTADDR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_INDWRSTADDR register from the beginning of the component. */
#define ALT_QSPI_INDWRSTADDR_OFST        0x78

/*
 * Register : Indirect Write Transfer Count Register - indwrcnt
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description             
 * :-------|:-------|:------|:-------------------------
 *  [31:0] | RW     | 0x0   | Indirect Number of Bytes
 * 
 */
/*
 * Field : Indirect Number of Bytes - value
 * 
 * This is the number of bytes that the indirect access will consume. This can be
 * bigger than the configured size of SRAM.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_INDWRCNT_VALUE register field. */
#define ALT_QSPI_INDWRCNT_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_INDWRCNT_VALUE register field. */
#define ALT_QSPI_INDWRCNT_VALUE_MSB        31
/* The width in bits of the ALT_QSPI_INDWRCNT_VALUE register field. */
#define ALT_QSPI_INDWRCNT_VALUE_WIDTH      32
/* The mask used to set the ALT_QSPI_INDWRCNT_VALUE register field value. */
#define ALT_QSPI_INDWRCNT_VALUE_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_INDWRCNT_VALUE register field value. */
#define ALT_QSPI_INDWRCNT_VALUE_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_INDWRCNT_VALUE register field. */
#define ALT_QSPI_INDWRCNT_VALUE_RESET      0x0
/* Extracts the ALT_QSPI_INDWRCNT_VALUE field value from a register. */
#define ALT_QSPI_INDWRCNT_VALUE_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_INDWRCNT_VALUE register field value suitable for setting the register. */
#define ALT_QSPI_INDWRCNT_VALUE_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_INDWRCNT.
 */
struct ALT_QSPI_INDWRCNT_s
{
    uint32_t  value : 32;  /* Indirect Number of Bytes */
};

/* The typedef declaration for register ALT_QSPI_INDWRCNT. */
typedef volatile struct ALT_QSPI_INDWRCNT_s  ALT_QSPI_INDWRCNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_INDWRCNT register from the beginning of the component. */
#define ALT_QSPI_INDWRCNT_OFST        0x7c

/*
 * Register : Flash Command Register - flashcmd
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description               
 * :--------|:-------|:------|:---------------------------
 *  [0]     | RW     | 0x0   | Execute Command           
 *  [1]     | R      | 0x0   | Command Execution Status  
 *  [6:2]   | ???    | 0x0   | *UNDEFINED*               
 *  [11:7]  | RW     | 0x0   | Number of Dummy Bytes     
 *  [14:12] | RW     | 0x0   | Number of Write Data Bytes
 *  [15]    | RW     | 0x0   | Write Data Enable         
 *  [17:16] | RW     | 0x0   | Number of Address Bytes   
 *  [18]    | RW     | 0x0   | Mode Bit Enable           
 *  [19]    | RW     | 0x0   | Command Address Enable    
 *  [22:20] | RW     | 0x0   | Number of Read Data Bytes 
 *  [23]    | RW     | 0x0   | Read Data Enable          
 *  [31:24] | RW     | 0x0   | Command Opcode            
 * 
 */
/*
 * Field : Execute Command - execcmd
 * 
 * Execute the command.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description    
 * :------------------------------------|:------|:----------------
 *  ALT_QSPI_FLSHCMD_EXECCMD_E_EXECUTE  | 0x1   | Execute Command
 *  ALT_QSPI_FLSHCMD_EXECCMD_E_NOACTION | 0x0   | No Action      
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_EXECCMD
 * 
 * Execute Command
 */
#define ALT_QSPI_FLSHCMD_EXECCMD_E_EXECUTE  0x1
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_EXECCMD
 * 
 * No Action
 */
#define ALT_QSPI_FLSHCMD_EXECCMD_E_NOACTION 0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMD_EXECCMD register field. */
#define ALT_QSPI_FLSHCMD_EXECCMD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMD_EXECCMD register field. */
#define ALT_QSPI_FLSHCMD_EXECCMD_MSB        0
/* The width in bits of the ALT_QSPI_FLSHCMD_EXECCMD register field. */
#define ALT_QSPI_FLSHCMD_EXECCMD_WIDTH      1
/* The mask used to set the ALT_QSPI_FLSHCMD_EXECCMD register field value. */
#define ALT_QSPI_FLSHCMD_EXECCMD_SET_MSK    0x00000001
/* The mask used to clear the ALT_QSPI_FLSHCMD_EXECCMD register field value. */
#define ALT_QSPI_FLSHCMD_EXECCMD_CLR_MSK    0xfffffffe
/* The reset value of the ALT_QSPI_FLSHCMD_EXECCMD register field. */
#define ALT_QSPI_FLSHCMD_EXECCMD_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMD_EXECCMD field value from a register. */
#define ALT_QSPI_FLSHCMD_EXECCMD_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_QSPI_FLSHCMD_EXECCMD register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMD_EXECCMD_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Command Execution Status - cmdexecstat
 * 
 * Command execution in progress.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                       | Value | Description             
 * :-------------------------------------------|:------|:-------------------------
 *  ALT_QSPI_FLSHCMD_CMDEXECSTAT_E_EXECUTESTAT | 0x1   | Command Execution Status
 *  ALT_QSPI_FLSHCMD_CMDEXECSTAT_E_NOACTION    | 0x0   | No Action               
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_CMDEXECSTAT
 * 
 * Command Execution Status
 */
#define ALT_QSPI_FLSHCMD_CMDEXECSTAT_E_EXECUTESTAT  0x1
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_CMDEXECSTAT
 * 
 * No Action
 */
#define ALT_QSPI_FLSHCMD_CMDEXECSTAT_E_NOACTION     0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMD_CMDEXECSTAT register field. */
#define ALT_QSPI_FLSHCMD_CMDEXECSTAT_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMD_CMDEXECSTAT register field. */
#define ALT_QSPI_FLSHCMD_CMDEXECSTAT_MSB        1
/* The width in bits of the ALT_QSPI_FLSHCMD_CMDEXECSTAT register field. */
#define ALT_QSPI_FLSHCMD_CMDEXECSTAT_WIDTH      1
/* The mask used to set the ALT_QSPI_FLSHCMD_CMDEXECSTAT register field value. */
#define ALT_QSPI_FLSHCMD_CMDEXECSTAT_SET_MSK    0x00000002
/* The mask used to clear the ALT_QSPI_FLSHCMD_CMDEXECSTAT register field value. */
#define ALT_QSPI_FLSHCMD_CMDEXECSTAT_CLR_MSK    0xfffffffd
/* The reset value of the ALT_QSPI_FLSHCMD_CMDEXECSTAT register field. */
#define ALT_QSPI_FLSHCMD_CMDEXECSTAT_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMD_CMDEXECSTAT field value from a register. */
#define ALT_QSPI_FLSHCMD_CMDEXECSTAT_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_QSPI_FLSHCMD_CMDEXECSTAT register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMD_CMDEXECSTAT_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Number of Dummy Bytes - numdummybytes
 * 
 * Set to the number of dummy bytes required This should be setup before triggering
 * the command via the execute field of this register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMD_NUMDUMMYBYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMD_NUMDUMMYBYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_MSB        11
/* The width in bits of the ALT_QSPI_FLSHCMD_NUMDUMMYBYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_WIDTH      5
/* The mask used to set the ALT_QSPI_FLSHCMD_NUMDUMMYBYTES register field value. */
#define ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_SET_MSK    0x00000f80
/* The mask used to clear the ALT_QSPI_FLSHCMD_NUMDUMMYBYTES register field value. */
#define ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_CLR_MSK    0xfffff07f
/* The reset value of the ALT_QSPI_FLSHCMD_NUMDUMMYBYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMD_NUMDUMMYBYTES field value from a register. */
#define ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_GET(value) (((value) & 0x00000f80) >> 7)
/* Produces a ALT_QSPI_FLSHCMD_NUMDUMMYBYTES register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMD_NUMDUMMYBYTES_SET(value) (((value) << 7) & 0x00000f80)

/*
 * Field : Number of Write Data Bytes - numwrdatabytes
 * 
 * Up to 8 Data bytes may be written using this command.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description 
 * :------------------------------------------|:------|:-------------
 *  ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE1 | 0x0   | Write 1 Byte
 *  ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE2 | 0x1   | Write 2 Byte
 *  ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE3 | 0x2   | Write 3 Byte
 *  ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE4 | 0x3   | Write 4 Byte
 *  ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE5 | 0x4   | Write 5 Byte
 *  ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE6 | 0x5   | Write 6 Byte
 *  ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE7 | 0x6   | Write 7 Byte
 *  ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE8 | 0x7   | Write 8 Byte
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMWRDATABYTES
 * 
 * Write 1 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE1   0x0
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMWRDATABYTES
 * 
 * Write 2 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE2   0x1
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMWRDATABYTES
 * 
 * Write 3 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE3   0x2
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMWRDATABYTES
 * 
 * Write 4 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE4   0x3
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMWRDATABYTES
 * 
 * Write 5 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE5   0x4
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMWRDATABYTES
 * 
 * Write 6 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE6   0x5
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMWRDATABYTES
 * 
 * Write 7 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE7   0x6
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMWRDATABYTES
 * 
 * Write 8 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_E_WRBYTE8   0x7

/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMD_NUMWRDATABYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMD_NUMWRDATABYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_MSB        14
/* The width in bits of the ALT_QSPI_FLSHCMD_NUMWRDATABYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_WIDTH      3
/* The mask used to set the ALT_QSPI_FLSHCMD_NUMWRDATABYTES register field value. */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_SET_MSK    0x00007000
/* The mask used to clear the ALT_QSPI_FLSHCMD_NUMWRDATABYTES register field value. */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_CLR_MSK    0xffff8fff
/* The reset value of the ALT_QSPI_FLSHCMD_NUMWRDATABYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMD_NUMWRDATABYTES field value from a register. */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_GET(value) (((value) & 0x00007000) >> 12)
/* Produces a ALT_QSPI_FLSHCMD_NUMWRDATABYTES register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMD_NUMWRDATABYTES_SET(value) (((value) << 12) & 0x00007000)

/*
 * Field : Write Data Enable - enwrdata
 * 
 * Set to 1 if the command specified in the command opcode field requires write
 * data bytes to be sent to the device.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                    | Value | Description                      
 * :----------------------------------------|:------|:----------------------------------
 *  ALT_QSPI_FLSHCMD_ENWRDATA_E_WRDATABYTES | 0x1   | Command requires write data bytes
 *  ALT_QSPI_FLSHCMD_ENWRDATA_E_NOACTION    | 0x0   | No Action                        
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_ENWRDATA
 * 
 * Command requires write data bytes
 */
#define ALT_QSPI_FLSHCMD_ENWRDATA_E_WRDATABYTES 0x1
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_ENWRDATA
 * 
 * No Action
 */
#define ALT_QSPI_FLSHCMD_ENWRDATA_E_NOACTION    0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMD_ENWRDATA register field. */
#define ALT_QSPI_FLSHCMD_ENWRDATA_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMD_ENWRDATA register field. */
#define ALT_QSPI_FLSHCMD_ENWRDATA_MSB        15
/* The width in bits of the ALT_QSPI_FLSHCMD_ENWRDATA register field. */
#define ALT_QSPI_FLSHCMD_ENWRDATA_WIDTH      1
/* The mask used to set the ALT_QSPI_FLSHCMD_ENWRDATA register field value. */
#define ALT_QSPI_FLSHCMD_ENWRDATA_SET_MSK    0x00008000
/* The mask used to clear the ALT_QSPI_FLSHCMD_ENWRDATA register field value. */
#define ALT_QSPI_FLSHCMD_ENWRDATA_CLR_MSK    0xffff7fff
/* The reset value of the ALT_QSPI_FLSHCMD_ENWRDATA register field. */
#define ALT_QSPI_FLSHCMD_ENWRDATA_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMD_ENWRDATA field value from a register. */
#define ALT_QSPI_FLSHCMD_ENWRDATA_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_QSPI_FLSHCMD_ENWRDATA register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMD_ENWRDATA_SET(value) (((value) << 15) & 0x00008000)

/*
 * Field : Number of Address Bytes - numaddrbytes
 * 
 * Set to the number of address bytes required (the address itself is programmed in
 * the FLASH COMMAND ADDRESS REGISTERS). This should be setup before triggering the
 * command via bit 0 of this register. 2'b00 : 1 address byte 2'b01 : 2 address
 * bytes 2'b10 : 3 address bytes 2'b11 : 4 address bytes
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description          
 * :------------------------------------------|:------|:----------------------
 *  ALT_QSPI_FLSHCMD_NUMADDRBYTES_E_ADDRBYTE1 | 0x0   | Write 1 Address Byte 
 *  ALT_QSPI_FLSHCMD_NUMADDRBYTES_E_ADDRBYTE2 | 0x1   | Write 2 Address Bytes
 *  ALT_QSPI_FLSHCMD_NUMADDRBYTES_E_ADDRBYTE3 | 0x2   | Write 3 Address Bytes
 *  ALT_QSPI_FLSHCMD_NUMADDRBYTES_E_ADDRBYTE4 | 0x3   | Write 4 Address Bytes
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMADDRBYTES
 * 
 * Write 1 Address Byte
 */
#define ALT_QSPI_FLSHCMD_NUMADDRBYTES_E_ADDRBYTE1   0x0
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMADDRBYTES
 * 
 * Write 2 Address Bytes
 */
#define ALT_QSPI_FLSHCMD_NUMADDRBYTES_E_ADDRBYTE2   0x1
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMADDRBYTES
 * 
 * Write 3 Address Bytes
 */
#define ALT_QSPI_FLSHCMD_NUMADDRBYTES_E_ADDRBYTE3   0x2
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMADDRBYTES
 * 
 * Write 4 Address Bytes
 */
#define ALT_QSPI_FLSHCMD_NUMADDRBYTES_E_ADDRBYTE4   0x3

/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMD_NUMADDRBYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMADDRBYTES_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMD_NUMADDRBYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMADDRBYTES_MSB        17
/* The width in bits of the ALT_QSPI_FLSHCMD_NUMADDRBYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMADDRBYTES_WIDTH      2
/* The mask used to set the ALT_QSPI_FLSHCMD_NUMADDRBYTES register field value. */
#define ALT_QSPI_FLSHCMD_NUMADDRBYTES_SET_MSK    0x00030000
/* The mask used to clear the ALT_QSPI_FLSHCMD_NUMADDRBYTES register field value. */
#define ALT_QSPI_FLSHCMD_NUMADDRBYTES_CLR_MSK    0xfffcffff
/* The reset value of the ALT_QSPI_FLSHCMD_NUMADDRBYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMADDRBYTES_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMD_NUMADDRBYTES field value from a register. */
#define ALT_QSPI_FLSHCMD_NUMADDRBYTES_GET(value) (((value) & 0x00030000) >> 16)
/* Produces a ALT_QSPI_FLSHCMD_NUMADDRBYTES register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMD_NUMADDRBYTES_SET(value) (((value) << 16) & 0x00030000)

/*
 * Field : Mode Bit Enable - enmodebit
 * 
 * Set to 1 to ensure the mode bits as defined in the Mode Bit Configuration
 * register are sent following the address bytes.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                   
 * :---------------------------------|:------|:-------------------------------
 *  ALT_QSPI_FLSHCMD_ENMODBIT_E_END  | 0x1   | Mode Bit follows address bytes
 *  ALT_QSPI_FLSHCMD_ENMODBIT_E_DISD | 0x0   | No Action                     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_ENMODBIT
 * 
 * Mode Bit follows address bytes
 */
#define ALT_QSPI_FLSHCMD_ENMODBIT_E_END     0x1
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_ENMODBIT
 * 
 * No Action
 */
#define ALT_QSPI_FLSHCMD_ENMODBIT_E_DISD    0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMD_ENMODBIT register field. */
#define ALT_QSPI_FLSHCMD_ENMODBIT_LSB        18
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMD_ENMODBIT register field. */
#define ALT_QSPI_FLSHCMD_ENMODBIT_MSB        18
/* The width in bits of the ALT_QSPI_FLSHCMD_ENMODBIT register field. */
#define ALT_QSPI_FLSHCMD_ENMODBIT_WIDTH      1
/* The mask used to set the ALT_QSPI_FLSHCMD_ENMODBIT register field value. */
#define ALT_QSPI_FLSHCMD_ENMODBIT_SET_MSK    0x00040000
/* The mask used to clear the ALT_QSPI_FLSHCMD_ENMODBIT register field value. */
#define ALT_QSPI_FLSHCMD_ENMODBIT_CLR_MSK    0xfffbffff
/* The reset value of the ALT_QSPI_FLSHCMD_ENMODBIT register field. */
#define ALT_QSPI_FLSHCMD_ENMODBIT_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMD_ENMODBIT field value from a register. */
#define ALT_QSPI_FLSHCMD_ENMODBIT_GET(value) (((value) & 0x00040000) >> 18)
/* Produces a ALT_QSPI_FLSHCMD_ENMODBIT register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMD_ENMODBIT_SET(value) (((value) << 18) & 0x00040000)

/*
 * Field : Command Address Enable - encmdaddr
 * 
 * If enabled, the command specified in bits 31:24 requires an address. This should
 * be setup before triggering the command via writing a 1 to the execute field.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                           
 * :----------------------------------|:------|:---------------------------------------
 *  ALT_QSPI_FLSHCMD_ENCMDADDR_E_END  | 0x1   | Command in bits 31:24 requires address
 *  ALT_QSPI_FLSHCMD_ENCMDADDR_E_DISD | 0x0   | No Action                             
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_ENCMDADDR
 * 
 * Command in bits 31:24 requires address
 */
#define ALT_QSPI_FLSHCMD_ENCMDADDR_E_END    0x1
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_ENCMDADDR
 * 
 * No Action
 */
#define ALT_QSPI_FLSHCMD_ENCMDADDR_E_DISD   0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMD_ENCMDADDR register field. */
#define ALT_QSPI_FLSHCMD_ENCMDADDR_LSB        19
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMD_ENCMDADDR register field. */
#define ALT_QSPI_FLSHCMD_ENCMDADDR_MSB        19
/* The width in bits of the ALT_QSPI_FLSHCMD_ENCMDADDR register field. */
#define ALT_QSPI_FLSHCMD_ENCMDADDR_WIDTH      1
/* The mask used to set the ALT_QSPI_FLSHCMD_ENCMDADDR register field value. */
#define ALT_QSPI_FLSHCMD_ENCMDADDR_SET_MSK    0x00080000
/* The mask used to clear the ALT_QSPI_FLSHCMD_ENCMDADDR register field value. */
#define ALT_QSPI_FLSHCMD_ENCMDADDR_CLR_MSK    0xfff7ffff
/* The reset value of the ALT_QSPI_FLSHCMD_ENCMDADDR register field. */
#define ALT_QSPI_FLSHCMD_ENCMDADDR_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMD_ENCMDADDR field value from a register. */
#define ALT_QSPI_FLSHCMD_ENCMDADDR_GET(value) (((value) & 0x00080000) >> 19)
/* Produces a ALT_QSPI_FLSHCMD_ENCMDADDR register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMD_ENCMDADDR_SET(value) (((value) << 19) & 0x00080000)

/*
 * Field : Number of Read Data Bytes - numrddatabytes
 * 
 * Up to 8 data bytes may be read using this command. Set to 0 for 1 byte and 7 for
 * 8 bytes.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description
 * :------------------------------------------|:------|:------------
 *  ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE1 | 0x0   | Read 1 Byte
 *  ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE2 | 0x1   | Read 2 Byte
 *  ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE3 | 0x2   | Read 3 Byte
 *  ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE4 | 0x3   | Read 4 Byte
 *  ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE5 | 0x4   | Read 5 Byte
 *  ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE6 | 0x5   | Read 6 Byte
 *  ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE7 | 0x6   | Read 7 Byte
 *  ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE8 | 0x7   | Read 8 Byte
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMRDDATABYTES
 * 
 * Read 1 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE1   0x0
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMRDDATABYTES
 * 
 * Read 2 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE2   0x1
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMRDDATABYTES
 * 
 * Read 3 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE3   0x2
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMRDDATABYTES
 * 
 * Read 4 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE4   0x3
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMRDDATABYTES
 * 
 * Read 5 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE5   0x4
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMRDDATABYTES
 * 
 * Read 6 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE6   0x5
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMRDDATABYTES
 * 
 * Read 7 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE7   0x6
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_NUMRDDATABYTES
 * 
 * Read 8 Byte
 */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_E_RDBYTE8   0x7

/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMD_NUMRDDATABYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_LSB        20
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMD_NUMRDDATABYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_MSB        22
/* The width in bits of the ALT_QSPI_FLSHCMD_NUMRDDATABYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_WIDTH      3
/* The mask used to set the ALT_QSPI_FLSHCMD_NUMRDDATABYTES register field value. */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_SET_MSK    0x00700000
/* The mask used to clear the ALT_QSPI_FLSHCMD_NUMRDDATABYTES register field value. */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_CLR_MSK    0xff8fffff
/* The reset value of the ALT_QSPI_FLSHCMD_NUMRDDATABYTES register field. */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMD_NUMRDDATABYTES field value from a register. */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_GET(value) (((value) & 0x00700000) >> 20)
/* Produces a ALT_QSPI_FLSHCMD_NUMRDDATABYTES register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMD_NUMRDDATABYTES_SET(value) (((value) << 20) & 0x00700000)

/*
 * Field : Read Data Enable - enrddata
 * 
 * If enabled, the command specified in the command opcode field (bits 31:24)
 * requires read data bytes to be received from the device.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description               
 * :-------------------------------------|:------|:---------------------------
 *  ALT_QSPI_FLSHCMD_ENRDDATA_E_EN       | 0x1   | Command Requires read data
 *  ALT_QSPI_FLSHCMD_ENRDDATA_E_NOACTION | 0x0   | No Action                 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_ENRDDATA
 * 
 * Command Requires read data
 */
#define ALT_QSPI_FLSHCMD_ENRDDATA_E_EN          0x1
/*
 * Enumerated value for register field ALT_QSPI_FLSHCMD_ENRDDATA
 * 
 * No Action
 */
#define ALT_QSPI_FLSHCMD_ENRDDATA_E_NOACTION    0x0

/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMD_ENRDDATA register field. */
#define ALT_QSPI_FLSHCMD_ENRDDATA_LSB        23
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMD_ENRDDATA register field. */
#define ALT_QSPI_FLSHCMD_ENRDDATA_MSB        23
/* The width in bits of the ALT_QSPI_FLSHCMD_ENRDDATA register field. */
#define ALT_QSPI_FLSHCMD_ENRDDATA_WIDTH      1
/* The mask used to set the ALT_QSPI_FLSHCMD_ENRDDATA register field value. */
#define ALT_QSPI_FLSHCMD_ENRDDATA_SET_MSK    0x00800000
/* The mask used to clear the ALT_QSPI_FLSHCMD_ENRDDATA register field value. */
#define ALT_QSPI_FLSHCMD_ENRDDATA_CLR_MSK    0xff7fffff
/* The reset value of the ALT_QSPI_FLSHCMD_ENRDDATA register field. */
#define ALT_QSPI_FLSHCMD_ENRDDATA_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMD_ENRDDATA field value from a register. */
#define ALT_QSPI_FLSHCMD_ENRDDATA_GET(value) (((value) & 0x00800000) >> 23)
/* Produces a ALT_QSPI_FLSHCMD_ENRDDATA register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMD_ENRDDATA_SET(value) (((value) << 23) & 0x00800000)

/*
 * Field : Command Opcode - cmdopcode
 * 
 * The command opcode field should be setup before triggering the command. For
 * example, 0x20 maps to SubSector Erase. Writeing to the execute field (bit 0) of
 * this register launches the command. NOTE : Using this approach to issue commands
 * to the device will make use of the instruction type of the device instruction
 * configuration register. If this field is set to 2'b00, then the command opcode,
 * command address, command dummy bytes and command data will all be transferred in
 * a serial fashion. If this field is set to 2'b01, then the command opcode,
 * command address, command dummy bytes and command data will all be transferred in
 * parallel using DQ0 and DQ1 pins. If this field is set to 2'b10, then the command
 * opcode, command address, command dummy bytes and command data will all be
 * transferred in parallel using DQ0, DQ1, DQ2 and DQ3 pins.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMD_CMDOPCODE register field. */
#define ALT_QSPI_FLSHCMD_CMDOPCODE_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMD_CMDOPCODE register field. */
#define ALT_QSPI_FLSHCMD_CMDOPCODE_MSB        31
/* The width in bits of the ALT_QSPI_FLSHCMD_CMDOPCODE register field. */
#define ALT_QSPI_FLSHCMD_CMDOPCODE_WIDTH      8
/* The mask used to set the ALT_QSPI_FLSHCMD_CMDOPCODE register field value. */
#define ALT_QSPI_FLSHCMD_CMDOPCODE_SET_MSK    0xff000000
/* The mask used to clear the ALT_QSPI_FLSHCMD_CMDOPCODE register field value. */
#define ALT_QSPI_FLSHCMD_CMDOPCODE_CLR_MSK    0x00ffffff
/* The reset value of the ALT_QSPI_FLSHCMD_CMDOPCODE register field. */
#define ALT_QSPI_FLSHCMD_CMDOPCODE_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMD_CMDOPCODE field value from a register. */
#define ALT_QSPI_FLSHCMD_CMDOPCODE_GET(value) (((value) & 0xff000000) >> 24)
/* Produces a ALT_QSPI_FLSHCMD_CMDOPCODE register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMD_CMDOPCODE_SET(value) (((value) << 24) & 0xff000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_FLSHCMD.
 */
struct ALT_QSPI_FLSHCMD_s
{
    uint32_t        execcmd        :  1;  /* Execute Command */
    const uint32_t  cmdexecstat    :  1;  /* Command Execution Status */
    uint32_t                       :  5;  /* *UNDEFINED* */
    uint32_t        numdummybytes  :  5;  /* Number of Dummy Bytes */
    uint32_t        numwrdatabytes :  3;  /* Number of Write Data Bytes */
    uint32_t        enwrdata       :  1;  /* Write Data Enable */
    uint32_t        numaddrbytes   :  2;  /* Number of Address Bytes */
    uint32_t        enmodebit      :  1;  /* Mode Bit Enable */
    uint32_t        encmdaddr      :  1;  /* Command Address Enable */
    uint32_t        numrddatabytes :  3;  /* Number of Read Data Bytes */
    uint32_t        enrddata       :  1;  /* Read Data Enable */
    uint32_t        cmdopcode      :  8;  /* Command Opcode */
};

/* The typedef declaration for register ALT_QSPI_FLSHCMD. */
typedef volatile struct ALT_QSPI_FLSHCMD_s  ALT_QSPI_FLSHCMD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_FLSHCMD register from the beginning of the component. */
#define ALT_QSPI_FLSHCMD_OFST        0x90

/*
 * Register : Flash Command Address Registers - flashcmdaddr
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description    
 * :-------|:-------|:------|:----------------
 *  [31:0] | RW     | 0x0   | Command Address
 * 
 */
/*
 * Field : Command Address - addr
 * 
 * This should be setup before triggering the command with execute field (bit 0) of
 * the Flash Command Control register. It is the address used by the command
 * specified in the opcode field (bits 31:24) of the Flash Command Control
 * register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMDADDR_ADDR register field. */
#define ALT_QSPI_FLSHCMDADDR_ADDR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMDADDR_ADDR register field. */
#define ALT_QSPI_FLSHCMDADDR_ADDR_MSB        31
/* The width in bits of the ALT_QSPI_FLSHCMDADDR_ADDR register field. */
#define ALT_QSPI_FLSHCMDADDR_ADDR_WIDTH      32
/* The mask used to set the ALT_QSPI_FLSHCMDADDR_ADDR register field value. */
#define ALT_QSPI_FLSHCMDADDR_ADDR_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_FLSHCMDADDR_ADDR register field value. */
#define ALT_QSPI_FLSHCMDADDR_ADDR_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_FLSHCMDADDR_ADDR register field. */
#define ALT_QSPI_FLSHCMDADDR_ADDR_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMDADDR_ADDR field value from a register. */
#define ALT_QSPI_FLSHCMDADDR_ADDR_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_FLSHCMDADDR_ADDR register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMDADDR_ADDR_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_FLSHCMDADDR.
 */
struct ALT_QSPI_FLSHCMDADDR_s
{
    uint32_t  addr : 32;  /* Command Address */
};

/* The typedef declaration for register ALT_QSPI_FLSHCMDADDR. */
typedef volatile struct ALT_QSPI_FLSHCMDADDR_s  ALT_QSPI_FLSHCMDADDR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_FLSHCMDADDR register from the beginning of the component. */
#define ALT_QSPI_FLSHCMDADDR_OFST        0x94

/*
 * Register : Flash Command Read Data Register (Lower) - flashcmdrddatalo
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                   
 * :-------|:-------|:------|:-------------------------------
 *  [31:0] | RW     | 0x0   | Command Read Data (Lower byte)
 * 
 */
/*
 * Field : Command Read Data (Lower byte) - data
 * 
 * This is the data that is returned by the flash device for any status or
 * configuration read operation carried out by triggering the event in the control
 * register. The register will be valid when the polling bit in the control
 * register is low.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMDRDDATALO_DATA register field. */
#define ALT_QSPI_FLSHCMDRDDATALO_DATA_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMDRDDATALO_DATA register field. */
#define ALT_QSPI_FLSHCMDRDDATALO_DATA_MSB        31
/* The width in bits of the ALT_QSPI_FLSHCMDRDDATALO_DATA register field. */
#define ALT_QSPI_FLSHCMDRDDATALO_DATA_WIDTH      32
/* The mask used to set the ALT_QSPI_FLSHCMDRDDATALO_DATA register field value. */
#define ALT_QSPI_FLSHCMDRDDATALO_DATA_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_FLSHCMDRDDATALO_DATA register field value. */
#define ALT_QSPI_FLSHCMDRDDATALO_DATA_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_FLSHCMDRDDATALO_DATA register field. */
#define ALT_QSPI_FLSHCMDRDDATALO_DATA_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMDRDDATALO_DATA field value from a register. */
#define ALT_QSPI_FLSHCMDRDDATALO_DATA_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_FLSHCMDRDDATALO_DATA register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMDRDDATALO_DATA_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_FLSHCMDRDDATALO.
 */
struct ALT_QSPI_FLSHCMDRDDATALO_s
{
    uint32_t  data : 32;  /* Command Read Data (Lower byte) */
};

/* The typedef declaration for register ALT_QSPI_FLSHCMDRDDATALO. */
typedef volatile struct ALT_QSPI_FLSHCMDRDDATALO_s  ALT_QSPI_FLSHCMDRDDATALO_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_FLSHCMDRDDATALO register from the beginning of the component. */
#define ALT_QSPI_FLSHCMDRDDATALO_OFST        0xa0

/*
 * Register : Flash Command Read Data Register (Upper) - flashcmdrddataup
 * 
 * Device Instruction Register
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                   
 * :-------|:-------|:------|:-------------------------------
 *  [31:0] | RW     | 0x0   | Command Read Data (Upper byte)
 * 
 */
/*
 * Field : Command Read Data (Upper byte) - data
 * 
 * This is the data that is returned by the FLASH device for any status or
 * configuration read operation carried out by triggering the event in the control
 * register. The register will be valid when the polling bit in the control
 * register is low.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMDRDDATAUP_DATA register field. */
#define ALT_QSPI_FLSHCMDRDDATAUP_DATA_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMDRDDATAUP_DATA register field. */
#define ALT_QSPI_FLSHCMDRDDATAUP_DATA_MSB        31
/* The width in bits of the ALT_QSPI_FLSHCMDRDDATAUP_DATA register field. */
#define ALT_QSPI_FLSHCMDRDDATAUP_DATA_WIDTH      32
/* The mask used to set the ALT_QSPI_FLSHCMDRDDATAUP_DATA register field value. */
#define ALT_QSPI_FLSHCMDRDDATAUP_DATA_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_FLSHCMDRDDATAUP_DATA register field value. */
#define ALT_QSPI_FLSHCMDRDDATAUP_DATA_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_FLSHCMDRDDATAUP_DATA register field. */
#define ALT_QSPI_FLSHCMDRDDATAUP_DATA_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMDRDDATAUP_DATA field value from a register. */
#define ALT_QSPI_FLSHCMDRDDATAUP_DATA_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_FLSHCMDRDDATAUP_DATA register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMDRDDATAUP_DATA_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_FLSHCMDRDDATAUP.
 */
struct ALT_QSPI_FLSHCMDRDDATAUP_s
{
    uint32_t  data : 32;  /* Command Read Data (Upper byte) */
};

/* The typedef declaration for register ALT_QSPI_FLSHCMDRDDATAUP. */
typedef volatile struct ALT_QSPI_FLSHCMDRDDATAUP_s  ALT_QSPI_FLSHCMDRDDATAUP_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_FLSHCMDRDDATAUP register from the beginning of the component. */
#define ALT_QSPI_FLSHCMDRDDATAUP_OFST        0xa4

/*
 * Register : Flash Command Write Data Register (Lower) - flashcmdwrdatalo
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [31:0] | RW     | 0x0   | Command Write Data Lower Byte
 * 
 */
/*
 * Field : Command Write Data Lower Byte - data
 * 
 * This is the command write data lower byte. This should be setup before
 * triggering the command with execute field (bit 0) of the Flash Command Control
 * register. It is the data that is to be written to the flash for any status or
 * configuration write operation carried out by triggering the event in the Flash
 * Command Control register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMDWRDATALO_DATA register field. */
#define ALT_QSPI_FLSHCMDWRDATALO_DATA_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMDWRDATALO_DATA register field. */
#define ALT_QSPI_FLSHCMDWRDATALO_DATA_MSB        31
/* The width in bits of the ALT_QSPI_FLSHCMDWRDATALO_DATA register field. */
#define ALT_QSPI_FLSHCMDWRDATALO_DATA_WIDTH      32
/* The mask used to set the ALT_QSPI_FLSHCMDWRDATALO_DATA register field value. */
#define ALT_QSPI_FLSHCMDWRDATALO_DATA_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_FLSHCMDWRDATALO_DATA register field value. */
#define ALT_QSPI_FLSHCMDWRDATALO_DATA_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_FLSHCMDWRDATALO_DATA register field. */
#define ALT_QSPI_FLSHCMDWRDATALO_DATA_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMDWRDATALO_DATA field value from a register. */
#define ALT_QSPI_FLSHCMDWRDATALO_DATA_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_FLSHCMDWRDATALO_DATA register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMDWRDATALO_DATA_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_FLSHCMDWRDATALO.
 */
struct ALT_QSPI_FLSHCMDWRDATALO_s
{
    uint32_t  data : 32;  /* Command Write Data Lower Byte */
};

/* The typedef declaration for register ALT_QSPI_FLSHCMDWRDATALO. */
typedef volatile struct ALT_QSPI_FLSHCMDWRDATALO_s  ALT_QSPI_FLSHCMDWRDATALO_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_FLSHCMDWRDATALO register from the beginning of the component. */
#define ALT_QSPI_FLSHCMDWRDATALO_OFST        0xa8

/*
 * Register : Flash Command Write Data Register (Upper) - flashcmdwrdataup
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [31:0] | RW     | 0x0   | ALT_QSPI_FLSHCMDWRDATAUP_DATA
 * 
 */
/*
 * Field : data
 * 
 * This is the command write data upper byte. This should be setup before
 * triggering the command with execute field (bit 0) of the Flash Command Control
 * register. It is the data that is to be written to the flash for any status or
 * configuration write operation carried out by triggering the event in the Flash
 * Command Control register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_FLSHCMDWRDATAUP_DATA register field. */
#define ALT_QSPI_FLSHCMDWRDATAUP_DATA_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_FLSHCMDWRDATAUP_DATA register field. */
#define ALT_QSPI_FLSHCMDWRDATAUP_DATA_MSB        31
/* The width in bits of the ALT_QSPI_FLSHCMDWRDATAUP_DATA register field. */
#define ALT_QSPI_FLSHCMDWRDATAUP_DATA_WIDTH      32
/* The mask used to set the ALT_QSPI_FLSHCMDWRDATAUP_DATA register field value. */
#define ALT_QSPI_FLSHCMDWRDATAUP_DATA_SET_MSK    0xffffffff
/* The mask used to clear the ALT_QSPI_FLSHCMDWRDATAUP_DATA register field value. */
#define ALT_QSPI_FLSHCMDWRDATAUP_DATA_CLR_MSK    0x00000000
/* The reset value of the ALT_QSPI_FLSHCMDWRDATAUP_DATA register field. */
#define ALT_QSPI_FLSHCMDWRDATAUP_DATA_RESET      0x0
/* Extracts the ALT_QSPI_FLSHCMDWRDATAUP_DATA field value from a register. */
#define ALT_QSPI_FLSHCMDWRDATAUP_DATA_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_QSPI_FLSHCMDWRDATAUP_DATA register field value suitable for setting the register. */
#define ALT_QSPI_FLSHCMDWRDATAUP_DATA_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_FLSHCMDWRDATAUP.
 */
struct ALT_QSPI_FLSHCMDWRDATAUP_s
{
    uint32_t  data : 32;  /* ALT_QSPI_FLSHCMDWRDATAUP_DATA */
};

/* The typedef declaration for register ALT_QSPI_FLSHCMDWRDATAUP. */
typedef volatile struct ALT_QSPI_FLSHCMDWRDATAUP_s  ALT_QSPI_FLSHCMDWRDATAUP_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_FLSHCMDWRDATAUP register from the beginning of the component. */
#define ALT_QSPI_FLSHCMDWRDATAUP_OFST        0xac

/*
 * Register : Module ID Register - moduleid
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset  | Description     
 * :--------|:-------|:-------|:-----------------
 *  [24:0]  | R      | 0x1001 | Module ID number
 *  [31:25] | ???    | 0x0    | *UNDEFINED*     
 * 
 */
/*
 * Field : Module ID number - value
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_QSPI_MODULEID_VALUE register field. */
#define ALT_QSPI_MODULEID_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_QSPI_MODULEID_VALUE register field. */
#define ALT_QSPI_MODULEID_VALUE_MSB        24
/* The width in bits of the ALT_QSPI_MODULEID_VALUE register field. */
#define ALT_QSPI_MODULEID_VALUE_WIDTH      25
/* The mask used to set the ALT_QSPI_MODULEID_VALUE register field value. */
#define ALT_QSPI_MODULEID_VALUE_SET_MSK    0x01ffffff
/* The mask used to clear the ALT_QSPI_MODULEID_VALUE register field value. */
#define ALT_QSPI_MODULEID_VALUE_CLR_MSK    0xfe000000
/* The reset value of the ALT_QSPI_MODULEID_VALUE register field. */
#define ALT_QSPI_MODULEID_VALUE_RESET      0x1001
/* Extracts the ALT_QSPI_MODULEID_VALUE field value from a register. */
#define ALT_QSPI_MODULEID_VALUE_GET(value) (((value) & 0x01ffffff) >> 0)
/* Produces a ALT_QSPI_MODULEID_VALUE register field value suitable for setting the register. */
#define ALT_QSPI_MODULEID_VALUE_SET(value) (((value) << 0) & 0x01ffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_QSPI_MODULEID.
 */
struct ALT_QSPI_MODULEID_s
{
    const uint32_t  value : 25;  /* Module ID number */
    uint32_t              :  7;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_QSPI_MODULEID. */
typedef volatile struct ALT_QSPI_MODULEID_s  ALT_QSPI_MODULEID_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_QSPI_MODULEID register from the beginning of the component. */
#define ALT_QSPI_MODULEID_OFST        0xfc

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_QSPI.
 */
struct ALT_QSPI_s
{
    volatile ALT_QSPI_CFG_t              cfg;                 /* ALT_QSPI_CFG */
    volatile ALT_QSPI_DEVRD_t            devrd;               /* ALT_QSPI_DEVRD */
    volatile ALT_QSPI_DEVWR_t            devwr;               /* ALT_QSPI_DEVWR */
    volatile ALT_QSPI_DELAY_t            delay;               /* ALT_QSPI_DELAY */
    volatile ALT_QSPI_RDDATACAP_t        rddatacap;           /* ALT_QSPI_RDDATACAP */
    volatile ALT_QSPI_DEVSZ_t            devsz;               /* ALT_QSPI_DEVSZ */
    volatile ALT_QSPI_SRAMPART_t         srampart;            /* ALT_QSPI_SRAMPART */
    volatile ALT_QSPI_INDADDRTRIG_t      indaddrtrig;         /* ALT_QSPI_INDADDRTRIG */
    volatile ALT_QSPI_DMAPER_t           dmaper;              /* ALT_QSPI_DMAPER */
    volatile ALT_QSPI_REMAPADDR_t        remapaddr;           /* ALT_QSPI_REMAPADDR */
    volatile ALT_QSPI_MODBIT_t           modebit;             /* ALT_QSPI_MODBIT */
    volatile ALT_QSPI_SRAMFILL_t         sramfill;            /* ALT_QSPI_SRAMFILL */
    volatile ALT_QSPI_TXTHRESH_t         txthresh;            /* ALT_QSPI_TXTHRESH */
    volatile ALT_QSPI_RXTHRESH_t         rxthresh;            /* ALT_QSPI_RXTHRESH */
    volatile uint32_t                    _pad_0x38_0x3f[2];   /* *UNDEFINED* */
    volatile ALT_QSPI_IRQSTAT_t          irqstat;             /* ALT_QSPI_IRQSTAT */
    volatile ALT_QSPI_IRQMSK_t           irqmask;             /* ALT_QSPI_IRQMSK */
    volatile uint32_t                    _pad_0x48_0x4f[2];   /* *UNDEFINED* */
    volatile ALT_QSPI_LOWWRPROT_t        lowwrprot;           /* ALT_QSPI_LOWWRPROT */
    volatile ALT_QSPI_UPPWRPROT_t        uppwrprot;           /* ALT_QSPI_UPPWRPROT */
    volatile ALT_QSPI_WRPROT_t           wrprot;              /* ALT_QSPI_WRPROT */
    volatile uint32_t                    _pad_0x5c_0x5f;      /* *UNDEFINED* */
    volatile ALT_QSPI_INDRD_t            indrd;               /* ALT_QSPI_INDRD */
    volatile ALT_QSPI_INDRDWATER_t       indrdwater;          /* ALT_QSPI_INDRDWATER */
    volatile ALT_QSPI_INDRDSTADDR_t      indrdstaddr;         /* ALT_QSPI_INDRDSTADDR */
    volatile ALT_QSPI_INDRDCNT_t         indrdcnt;            /* ALT_QSPI_INDRDCNT */
    volatile ALT_QSPI_INDWR_t            indwr;               /* ALT_QSPI_INDWR */
    volatile ALT_QSPI_INDWRWATER_t       indwrwater;          /* ALT_QSPI_INDWRWATER */
    volatile ALT_QSPI_INDWRSTADDR_t      indwrstaddr;         /* ALT_QSPI_INDWRSTADDR */
    volatile ALT_QSPI_INDWRCNT_t         indwrcnt;            /* ALT_QSPI_INDWRCNT */
    volatile uint32_t                    _pad_0x80_0x8f[4];   /* *UNDEFINED* */
    volatile ALT_QSPI_FLSHCMD_t          flashcmd;            /* ALT_QSPI_FLSHCMD */
    volatile ALT_QSPI_FLSHCMDADDR_t      flashcmdaddr;        /* ALT_QSPI_FLSHCMDADDR */
    volatile uint32_t                    _pad_0x98_0x9f[2];   /* *UNDEFINED* */
    volatile ALT_QSPI_FLSHCMDRDDATALO_t  flashcmdrddatalo;    /* ALT_QSPI_FLSHCMDRDDATALO */
    volatile ALT_QSPI_FLSHCMDRDDATAUP_t  flashcmdrddataup;    /* ALT_QSPI_FLSHCMDRDDATAUP */
    volatile ALT_QSPI_FLSHCMDWRDATALO_t  flashcmdwrdatalo;    /* ALT_QSPI_FLSHCMDWRDATALO */
    volatile ALT_QSPI_FLSHCMDWRDATAUP_t  flashcmdwrdataup;    /* ALT_QSPI_FLSHCMDWRDATAUP */
    volatile uint32_t                    _pad_0xb0_0xfb[19];  /* *UNDEFINED* */
    volatile ALT_QSPI_MODULEID_t         moduleid;            /* ALT_QSPI_MODULEID */
};

/* The typedef declaration for register group ALT_QSPI. */
typedef volatile struct ALT_QSPI_s  ALT_QSPI_t;
/* The struct declaration for the raw register contents of register group ALT_QSPI. */
struct ALT_QSPI_raw_s
{
    volatile uint32_t  cfg;                 /* ALT_QSPI_CFG */
    volatile uint32_t  devrd;               /* ALT_QSPI_DEVRD */
    volatile uint32_t  devwr;               /* ALT_QSPI_DEVWR */
    volatile uint32_t  delay;               /* ALT_QSPI_DELAY */
    volatile uint32_t  rddatacap;           /* ALT_QSPI_RDDATACAP */
    volatile uint32_t  devsz;               /* ALT_QSPI_DEVSZ */
    volatile uint32_t  srampart;            /* ALT_QSPI_SRAMPART */
    volatile uint32_t  indaddrtrig;         /* ALT_QSPI_INDADDRTRIG */
    volatile uint32_t  dmaper;              /* ALT_QSPI_DMAPER */
    volatile uint32_t  remapaddr;           /* ALT_QSPI_REMAPADDR */
    volatile uint32_t  modebit;             /* ALT_QSPI_MODBIT */
    volatile uint32_t  sramfill;            /* ALT_QSPI_SRAMFILL */
    volatile uint32_t  txthresh;            /* ALT_QSPI_TXTHRESH */
    volatile uint32_t  rxthresh;            /* ALT_QSPI_RXTHRESH */
    volatile uint32_t  _pad_0x38_0x3f[2];   /* *UNDEFINED* */
    volatile uint32_t  irqstat;             /* ALT_QSPI_IRQSTAT */
    volatile uint32_t  irqmask;             /* ALT_QSPI_IRQMSK */
    volatile uint32_t  _pad_0x48_0x4f[2];   /* *UNDEFINED* */
    volatile uint32_t  lowwrprot;           /* ALT_QSPI_LOWWRPROT */
    volatile uint32_t  uppwrprot;           /* ALT_QSPI_UPPWRPROT */
    volatile uint32_t  wrprot;              /* ALT_QSPI_WRPROT */
    volatile uint32_t  _pad_0x5c_0x5f;      /* *UNDEFINED* */
    volatile uint32_t  indrd;               /* ALT_QSPI_INDRD */
    volatile uint32_t  indrdwater;          /* ALT_QSPI_INDRDWATER */
    volatile uint32_t  indrdstaddr;         /* ALT_QSPI_INDRDSTADDR */
    volatile uint32_t  indrdcnt;            /* ALT_QSPI_INDRDCNT */
    volatile uint32_t  indwr;               /* ALT_QSPI_INDWR */
    volatile uint32_t  indwrwater;          /* ALT_QSPI_INDWRWATER */
    volatile uint32_t  indwrstaddr;         /* ALT_QSPI_INDWRSTADDR */
    volatile uint32_t  indwrcnt;            /* ALT_QSPI_INDWRCNT */
    volatile uint32_t  _pad_0x80_0x8f[4];   /* *UNDEFINED* */
    volatile uint32_t  flashcmd;            /* ALT_QSPI_FLSHCMD */
    volatile uint32_t  flashcmdaddr;        /* ALT_QSPI_FLSHCMDADDR */
    volatile uint32_t  _pad_0x98_0x9f[2];   /* *UNDEFINED* */
    volatile uint32_t  flashcmdrddatalo;    /* ALT_QSPI_FLSHCMDRDDATALO */
    volatile uint32_t  flashcmdrddataup;    /* ALT_QSPI_FLSHCMDRDDATAUP */
    volatile uint32_t  flashcmdwrdatalo;    /* ALT_QSPI_FLSHCMDWRDATALO */
    volatile uint32_t  flashcmdwrdataup;    /* ALT_QSPI_FLSHCMDWRDATAUP */
    volatile uint32_t  _pad_0xb0_0xfb[19];  /* *UNDEFINED* */
    volatile uint32_t  moduleid;            /* ALT_QSPI_MODULEID */
};

/* The typedef declaration for the raw register contents of register group ALT_QSPI. */
typedef volatile struct ALT_QSPI_raw_s  ALT_QSPI_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_QSPI_H__ */

