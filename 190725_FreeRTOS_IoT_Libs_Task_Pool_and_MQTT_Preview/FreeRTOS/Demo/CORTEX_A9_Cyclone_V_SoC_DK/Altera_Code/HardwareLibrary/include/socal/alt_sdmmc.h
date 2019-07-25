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

/* Altera - ALT_SDMMC */

#ifndef __ALTERA_ALT_SDMMC_H__
#define __ALTERA_ALT_SDMMC_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : SDMMC Module - ALT_SDMMC
 * SDMMC Module
 * 
 * Registers in the SD/MMC module
 * 
 */
/*
 * Register : Control Register - ctrl
 * 
 * Sets various operating condiitions.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                  
 * :--------|:-------|:------|:------------------------------
 *  [0]     | RW     | 0x0   | Controller Reset             
 *  [1]     | RW     | 0x0   | FIFO Reset                   
 *  [2]     | RW     | 0x0   | Dma Reset                    
 *  [3]     | ???    | 0x0   | *UNDEFINED*                  
 *  [4]     | RW     | 0x0   | Int Enable                   
 *  [5]     | ???    | 0x0   | *UNDEFINED*                  
 *  [6]     | RW     | 0x0   | Read Wait                    
 *  [7]     | RW     | 0x0   | Send Irq Response            
 *  [8]     | RW     | 0x0   | Abort Read Data              
 *  [9]     | RW     | 0x0   | Send CCSD                    
 *  [10]    | RW     | 0x0   | Send Auto Stop CCSD          
 *  [11]    | RW     | 0x0   | Ceata Device Interrupt Status
 *  [24:12] | ???    | 0x0   | *UNDEFINED*                  
 *  [25]    | RW     | 0x0   | Use Internal DMAC            
 *  [31:26] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : Controller Reset - controller_reset
 * 
 * This bit resets the controller. This bit is auto-cleared after two l4_mp_clk and
 * two sdmmc_clk clock cycles. This resets:
 * 
 * * BIU/CIU interface
 * 
 * * CIU and state machines
 * 
 * * abort_read_data, send_irq_response, and read_wait bits of control register
 * 
 * * start_cmd bit of command register
 * 
 * Does not affect any registers, DMA interface, FIFO or host interrupts.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description            
 * :------------------------------------|:------|:------------------------
 *  ALT_SDMMC_CTL_CTLLER_RST_E_NOCHANGE | 0x0   | No change -default     
 *  ALT_SDMMC_CTL_CTLLER_RST_E_ACTIVATE | 0x1   | Reset SD/MMC controller
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CTL_CTLLER_RST
 * 
 * No change -default
 */
#define ALT_SDMMC_CTL_CTLLER_RST_E_NOCHANGE 0x0
/*
 * Enumerated value for register field ALT_SDMMC_CTL_CTLLER_RST
 * 
 * Reset SD/MMC controller
 */
#define ALT_SDMMC_CTL_CTLLER_RST_E_ACTIVATE 0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CTL_CTLLER_RST register field. */
#define ALT_SDMMC_CTL_CTLLER_RST_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CTL_CTLLER_RST register field. */
#define ALT_SDMMC_CTL_CTLLER_RST_MSB        0
/* The width in bits of the ALT_SDMMC_CTL_CTLLER_RST register field. */
#define ALT_SDMMC_CTL_CTLLER_RST_WIDTH      1
/* The mask used to set the ALT_SDMMC_CTL_CTLLER_RST register field value. */
#define ALT_SDMMC_CTL_CTLLER_RST_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_CTL_CTLLER_RST register field value. */
#define ALT_SDMMC_CTL_CTLLER_RST_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_CTL_CTLLER_RST register field. */
#define ALT_SDMMC_CTL_CTLLER_RST_RESET      0x0
/* Extracts the ALT_SDMMC_CTL_CTLLER_RST field value from a register. */
#define ALT_SDMMC_CTL_CTLLER_RST_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_CTL_CTLLER_RST register field value suitable for setting the register. */
#define ALT_SDMMC_CTL_CTLLER_RST_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : FIFO Reset - fifo_reset
 * 
 * This bit resets the FIFO. This bit is auto-cleared after completion of reset
 * operation.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                              
 * :----------------------------------|:------|:------------------------------------------
 *  ALT_SDMMC_CTL_FIFO_RST_E_NOCHANGE | 0x0   | No change                                
 *  ALT_SDMMC_CTL_FIFO_RST_E_ACTIVATE | 0x1   | Reset to data FIFO To reset FIFO pointers
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CTL_FIFO_RST
 * 
 * No change
 */
#define ALT_SDMMC_CTL_FIFO_RST_E_NOCHANGE   0x0
/*
 * Enumerated value for register field ALT_SDMMC_CTL_FIFO_RST
 * 
 * Reset to data FIFO To reset FIFO pointers
 */
#define ALT_SDMMC_CTL_FIFO_RST_E_ACTIVATE   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CTL_FIFO_RST register field. */
#define ALT_SDMMC_CTL_FIFO_RST_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CTL_FIFO_RST register field. */
#define ALT_SDMMC_CTL_FIFO_RST_MSB        1
/* The width in bits of the ALT_SDMMC_CTL_FIFO_RST register field. */
#define ALT_SDMMC_CTL_FIFO_RST_WIDTH      1
/* The mask used to set the ALT_SDMMC_CTL_FIFO_RST register field value. */
#define ALT_SDMMC_CTL_FIFO_RST_SET_MSK    0x00000002
/* The mask used to clear the ALT_SDMMC_CTL_FIFO_RST register field value. */
#define ALT_SDMMC_CTL_FIFO_RST_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SDMMC_CTL_FIFO_RST register field. */
#define ALT_SDMMC_CTL_FIFO_RST_RESET      0x0
/* Extracts the ALT_SDMMC_CTL_FIFO_RST field value from a register. */
#define ALT_SDMMC_CTL_FIFO_RST_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SDMMC_CTL_FIFO_RST register field value suitable for setting the register. */
#define ALT_SDMMC_CTL_FIFO_RST_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Dma Reset - dma_reset
 * 
 * This bit resets the DMA interface control logic
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                               
 * :---------------------------------|:------|:-------------------------------------------
 *  ALT_SDMMC_CTL_DMA_RST_E_NOCHANGE | 0x0   | No change                                 
 *  ALT_SDMMC_CTL_DMA_RST_E_ACTIVATE | 0x1   | Reset internal DMA interface control logic
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CTL_DMA_RST
 * 
 * No change
 */
#define ALT_SDMMC_CTL_DMA_RST_E_NOCHANGE    0x0
/*
 * Enumerated value for register field ALT_SDMMC_CTL_DMA_RST
 * 
 * Reset internal DMA interface control logic
 */
#define ALT_SDMMC_CTL_DMA_RST_E_ACTIVATE    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CTL_DMA_RST register field. */
#define ALT_SDMMC_CTL_DMA_RST_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CTL_DMA_RST register field. */
#define ALT_SDMMC_CTL_DMA_RST_MSB        2
/* The width in bits of the ALT_SDMMC_CTL_DMA_RST register field. */
#define ALT_SDMMC_CTL_DMA_RST_WIDTH      1
/* The mask used to set the ALT_SDMMC_CTL_DMA_RST register field value. */
#define ALT_SDMMC_CTL_DMA_RST_SET_MSK    0x00000004
/* The mask used to clear the ALT_SDMMC_CTL_DMA_RST register field value. */
#define ALT_SDMMC_CTL_DMA_RST_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SDMMC_CTL_DMA_RST register field. */
#define ALT_SDMMC_CTL_DMA_RST_RESET      0x0
/* Extracts the ALT_SDMMC_CTL_DMA_RST field value from a register. */
#define ALT_SDMMC_CTL_DMA_RST_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SDMMC_CTL_DMA_RST register field value suitable for setting the register. */
#define ALT_SDMMC_CTL_DMA_RST_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Int Enable - int_enable
 * 
 * This bit enables and disable interrupts if one or more unmasked interrupts are
 * set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description       
 * :----------------------------|:------|:-------------------
 *  ALT_SDMMC_CTL_INT_EN_E_DISD | 0x0   | Disable Interrupts
 *  ALT_SDMMC_CTL_INT_EN_E_END  | 0x1   | Enable interrupts 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CTL_INT_EN
 * 
 * Disable Interrupts
 */
#define ALT_SDMMC_CTL_INT_EN_E_DISD 0x0
/*
 * Enumerated value for register field ALT_SDMMC_CTL_INT_EN
 * 
 * Enable interrupts
 */
#define ALT_SDMMC_CTL_INT_EN_E_END  0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CTL_INT_EN register field. */
#define ALT_SDMMC_CTL_INT_EN_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CTL_INT_EN register field. */
#define ALT_SDMMC_CTL_INT_EN_MSB        4
/* The width in bits of the ALT_SDMMC_CTL_INT_EN register field. */
#define ALT_SDMMC_CTL_INT_EN_WIDTH      1
/* The mask used to set the ALT_SDMMC_CTL_INT_EN register field value. */
#define ALT_SDMMC_CTL_INT_EN_SET_MSK    0x00000010
/* The mask used to clear the ALT_SDMMC_CTL_INT_EN register field value. */
#define ALT_SDMMC_CTL_INT_EN_CLR_MSK    0xffffffef
/* The reset value of the ALT_SDMMC_CTL_INT_EN register field. */
#define ALT_SDMMC_CTL_INT_EN_RESET      0x0
/* Extracts the ALT_SDMMC_CTL_INT_EN field value from a register. */
#define ALT_SDMMC_CTL_INT_EN_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SDMMC_CTL_INT_EN register field value suitable for setting the register. */
#define ALT_SDMMC_CTL_INT_EN_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Read Wait - read_wait
 * 
 * For sending read-wait to SDIO cards.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description     
 * :---------------------------------|:------|:-----------------
 *  ALT_SDMMC_CTL_RD_WAIT_E_DEASSERT | 0x0   | Read Wait       
 *  ALT_SDMMC_CTL_RD_WAIT_E_ASSERT   | 0x1   | Assert Read Wait
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CTL_RD_WAIT
 * 
 * Read Wait
 */
#define ALT_SDMMC_CTL_RD_WAIT_E_DEASSERT    0x0
/*
 * Enumerated value for register field ALT_SDMMC_CTL_RD_WAIT
 * 
 * Assert Read Wait
 */
#define ALT_SDMMC_CTL_RD_WAIT_E_ASSERT      0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CTL_RD_WAIT register field. */
#define ALT_SDMMC_CTL_RD_WAIT_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CTL_RD_WAIT register field. */
#define ALT_SDMMC_CTL_RD_WAIT_MSB        6
/* The width in bits of the ALT_SDMMC_CTL_RD_WAIT register field. */
#define ALT_SDMMC_CTL_RD_WAIT_WIDTH      1
/* The mask used to set the ALT_SDMMC_CTL_RD_WAIT register field value. */
#define ALT_SDMMC_CTL_RD_WAIT_SET_MSK    0x00000040
/* The mask used to clear the ALT_SDMMC_CTL_RD_WAIT register field value. */
#define ALT_SDMMC_CTL_RD_WAIT_CLR_MSK    0xffffffbf
/* The reset value of the ALT_SDMMC_CTL_RD_WAIT register field. */
#define ALT_SDMMC_CTL_RD_WAIT_RESET      0x0
/* Extracts the ALT_SDMMC_CTL_RD_WAIT field value from a register. */
#define ALT_SDMMC_CTL_RD_WAIT_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_SDMMC_CTL_RD_WAIT register field value suitable for setting the register. */
#define ALT_SDMMC_CTL_RD_WAIT_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Send Irq Response - send_irq_response
 * 
 * Bit automatically clears once response is sent. To wait for MMC card interrupts,
 * host issues CMD40, and SD/MMC waits for interrupt response from MMC card(s). In
 * meantime, if host wants SD/MMC to exit waiting for interrupt state, it can set
 * this bit, at which time SD/MMC command state-machine sends CMD40 response on bus
 * and returns to idle state.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                       | Value | Description           
 * :-------------------------------------------|:------|:-----------------------
 *  ALT_SDMMC_CTL_SEND_IRQ_RESPONSE_E_NOCHANGE | 0x0   | No change             
 *  ALT_SDMMC_CTL_SEND_IRQ_RESPONSE_E_ACTIVATE | 0x1   | Send auto IRQ response
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CTL_SEND_IRQ_RESPONSE
 * 
 * No change
 */
#define ALT_SDMMC_CTL_SEND_IRQ_RESPONSE_E_NOCHANGE  0x0
/*
 * Enumerated value for register field ALT_SDMMC_CTL_SEND_IRQ_RESPONSE
 * 
 * Send auto IRQ response
 */
#define ALT_SDMMC_CTL_SEND_IRQ_RESPONSE_E_ACTIVATE  0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CTL_SEND_IRQ_RESPONSE register field. */
#define ALT_SDMMC_CTL_SEND_IRQ_RESPONSE_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CTL_SEND_IRQ_RESPONSE register field. */
#define ALT_SDMMC_CTL_SEND_IRQ_RESPONSE_MSB        7
/* The width in bits of the ALT_SDMMC_CTL_SEND_IRQ_RESPONSE register field. */
#define ALT_SDMMC_CTL_SEND_IRQ_RESPONSE_WIDTH      1
/* The mask used to set the ALT_SDMMC_CTL_SEND_IRQ_RESPONSE register field value. */
#define ALT_SDMMC_CTL_SEND_IRQ_RESPONSE_SET_MSK    0x00000080
/* The mask used to clear the ALT_SDMMC_CTL_SEND_IRQ_RESPONSE register field value. */
#define ALT_SDMMC_CTL_SEND_IRQ_RESPONSE_CLR_MSK    0xffffff7f
/* The reset value of the ALT_SDMMC_CTL_SEND_IRQ_RESPONSE register field. */
#define ALT_SDMMC_CTL_SEND_IRQ_RESPONSE_RESET      0x0
/* Extracts the ALT_SDMMC_CTL_SEND_IRQ_RESPONSE field value from a register. */
#define ALT_SDMMC_CTL_SEND_IRQ_RESPONSE_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_SDMMC_CTL_SEND_IRQ_RESPONSE register field value suitable for setting the register. */
#define ALT_SDMMC_CTL_SEND_IRQ_RESPONSE_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Abort Read Data - abort_read_data
 * 
 * After suspend command is issued during read-transfer, software polls card to
 * find when suspend happened. Once suspend occurs software sets bit to reset data
 * state-machine, which is waiting for next block of data. Bit automatically clears
 * once data statemachine resets to idle. Used in SDIO card suspend sequence.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description
 * :-------------------------------------|:------|:------------
 *  ALT_SDMMC_CTL_ABT_RD_DATA_E_NOCHANGE | 0x0   | No change  
 *  ALT_SDMMC_CTL_ABT_RD_DATA_E_ACTIVATE | 0x1   | Abort Read 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CTL_ABT_RD_DATA
 * 
 * No change
 */
#define ALT_SDMMC_CTL_ABT_RD_DATA_E_NOCHANGE    0x0
/*
 * Enumerated value for register field ALT_SDMMC_CTL_ABT_RD_DATA
 * 
 * Abort Read
 */
#define ALT_SDMMC_CTL_ABT_RD_DATA_E_ACTIVATE    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CTL_ABT_RD_DATA register field. */
#define ALT_SDMMC_CTL_ABT_RD_DATA_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CTL_ABT_RD_DATA register field. */
#define ALT_SDMMC_CTL_ABT_RD_DATA_MSB        8
/* The width in bits of the ALT_SDMMC_CTL_ABT_RD_DATA register field. */
#define ALT_SDMMC_CTL_ABT_RD_DATA_WIDTH      1
/* The mask used to set the ALT_SDMMC_CTL_ABT_RD_DATA register field value. */
#define ALT_SDMMC_CTL_ABT_RD_DATA_SET_MSK    0x00000100
/* The mask used to clear the ALT_SDMMC_CTL_ABT_RD_DATA register field value. */
#define ALT_SDMMC_CTL_ABT_RD_DATA_CLR_MSK    0xfffffeff
/* The reset value of the ALT_SDMMC_CTL_ABT_RD_DATA register field. */
#define ALT_SDMMC_CTL_ABT_RD_DATA_RESET      0x0
/* Extracts the ALT_SDMMC_CTL_ABT_RD_DATA field value from a register. */
#define ALT_SDMMC_CTL_ABT_RD_DATA_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_SDMMC_CTL_ABT_RD_DATA register field value suitable for setting the register. */
#define ALT_SDMMC_CTL_ABT_RD_DATA_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Send CCSD - send_ccsd
 * 
 * When set, SD/MMC sends CCSD to CE-ATA device. Software sets this bit only if
 * current command is expecting CCS (that is, RW_BLK) and interrupts are enabled in
 * CE-ATA device. Once the CCSD pattern is sent to device, SD/MMC automatically
 * clears send_ccsd bit. It also sets Command Done (CD) bit in RINTSTS register and
 * generates interrupt to host if Command Done interrupt is not masked.
 * 
 * NOTE: Once send_ccsd bit is set, it takes two card clock cycles to drive the
 * CCSD on the CMD line. Due to this, during the boundary conditions it may happen
 * that CCSD is sent to the CE-ATA device, even if the device signalled CCS.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                                     
 * :-----------------------------------|:------|:-------------------------------------------------
 *  ALT_SDMMC_CTL_SEND_CCSD_E_DEASSERT | 0x0   | Clear bit if SD/MMC does not reset the bit      
 *  ALT_SDMMC_CTL_SEND_CCSD_E_ASSERT   | 0x1   | Send Command Completion Signal Disable (CCSD) to
 * :                                   |       | CE-ATA device                                   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CTL_SEND_CCSD
 * 
 * Clear bit if SD/MMC does not reset the bit
 */
#define ALT_SDMMC_CTL_SEND_CCSD_E_DEASSERT  0x0
/*
 * Enumerated value for register field ALT_SDMMC_CTL_SEND_CCSD
 * 
 * Send Command Completion Signal Disable (CCSD) to CE-ATA device
 */
#define ALT_SDMMC_CTL_SEND_CCSD_E_ASSERT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CTL_SEND_CCSD register field. */
#define ALT_SDMMC_CTL_SEND_CCSD_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CTL_SEND_CCSD register field. */
#define ALT_SDMMC_CTL_SEND_CCSD_MSB        9
/* The width in bits of the ALT_SDMMC_CTL_SEND_CCSD register field. */
#define ALT_SDMMC_CTL_SEND_CCSD_WIDTH      1
/* The mask used to set the ALT_SDMMC_CTL_SEND_CCSD register field value. */
#define ALT_SDMMC_CTL_SEND_CCSD_SET_MSK    0x00000200
/* The mask used to clear the ALT_SDMMC_CTL_SEND_CCSD register field value. */
#define ALT_SDMMC_CTL_SEND_CCSD_CLR_MSK    0xfffffdff
/* The reset value of the ALT_SDMMC_CTL_SEND_CCSD register field. */
#define ALT_SDMMC_CTL_SEND_CCSD_RESET      0x0
/* Extracts the ALT_SDMMC_CTL_SEND_CCSD field value from a register. */
#define ALT_SDMMC_CTL_SEND_CCSD_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_SDMMC_CTL_SEND_CCSD register field value suitable for setting the register. */
#define ALT_SDMMC_CTL_SEND_CCSD_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Send Auto Stop CCSD - send_auto_stop_ccsd
 * 
 * Always set send_auto_stop_ccsd and send_ccsd bits together; send_auto_stop_ccsd
 * should not be set independent of send_ccsd. When set, SD/MMC automatically sends
 * internally generated STOP command (CMD12) to CE-ATA device. After sending
 * internally-generated STOP command, Auto Command Done (ACD) bit in RINTSTS is set
 * and generates interrupt to host if Auto CommandDone interrupt is not masked.
 * After sending the CCSD, SD/MMC automatically clears send_auto_stop_ccsd bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                         | Value | Description                               
 * :---------------------------------------------|:------|:-------------------------------------------
 *  ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD_E_DEASSERT | 0x0   | Clear bit if SD/MMC does not reset the bit
 *  ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD_E_ASSERT   | 0x1   | Send internally generated STOP.           
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD
 * 
 * Clear bit if SD/MMC does not reset the bit
 */
#define ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD_E_DEASSERT    0x0
/*
 * Enumerated value for register field ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD
 * 
 * Send internally generated STOP.
 */
#define ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD_E_ASSERT      0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD register field. */
#define ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD register field. */
#define ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD_MSB        10
/* The width in bits of the ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD register field. */
#define ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD_WIDTH      1
/* The mask used to set the ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD register field value. */
#define ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD_SET_MSK    0x00000400
/* The mask used to clear the ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD register field value. */
#define ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD_CLR_MSK    0xfffffbff
/* The reset value of the ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD register field. */
#define ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD_RESET      0x0
/* Extracts the ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD field value from a register. */
#define ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD register field value suitable for setting the register. */
#define ALT_SDMMC_CTL_SEND_AUTO_STOP_CCSD_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Ceata Device Interrupt Status - ceata_device_interrupt_status
 * 
 * Software should appropriately write to this bit after power-on reset or any
 * other reset to CE-ATA device. After reset, usually CE-ATA device interrupt is
 * disabled (nIEN = 1). If the host enables CE-ATA device interrupt, then software
 * should set this bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                       | Value | Description                            
 * :-------------------------------------------|:------|:----------------------------------------
 *  ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT_E_DISD | 0x0   | Interrupts not enabled in CE-ATA device
 *  ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT_E_END  | 0x1   | Interrupts are enabled in CE-ATA device
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT
 * 
 * Interrupts not enabled in CE-ATA device
 */
#define ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT_E_DISD  0x0
/*
 * Enumerated value for register field ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT
 * 
 * Interrupts are enabled in CE-ATA device
 */
#define ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT_E_END   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT register field. */
#define ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT register field. */
#define ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT_MSB        11
/* The width in bits of the ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT register field. */
#define ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT_WIDTH      1
/* The mask used to set the ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT register field value. */
#define ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT_SET_MSK    0x00000800
/* The mask used to clear the ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT register field value. */
#define ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT register field. */
#define ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT_RESET      0x0
/* Extracts the ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT field value from a register. */
#define ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT register field value suitable for setting the register. */
#define ALT_SDMMC_CTL_CEATA_DEVICE_INT_STAT_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : Use Internal DMAC - use_internal_dmac
 * 
 * Enable and Disable Internal DMA transfers.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description                                
 * :---------------------------------------|:------|:--------------------------------------------
 *  ALT_SDMMC_CTL_USE_INTERNAL_DMAC_E_DISD | 0x0   | The host performs data transfers thru slave
 * :                                       |       | interface                                  
 *  ALT_SDMMC_CTL_USE_INTERNAL_DMAC_E_END  | 0x1   | Internal DMAC used for data transfer       
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CTL_USE_INTERNAL_DMAC
 * 
 * The host performs data transfers thru slave interface
 */
#define ALT_SDMMC_CTL_USE_INTERNAL_DMAC_E_DISD  0x0
/*
 * Enumerated value for register field ALT_SDMMC_CTL_USE_INTERNAL_DMAC
 * 
 * Internal DMAC used for data transfer
 */
#define ALT_SDMMC_CTL_USE_INTERNAL_DMAC_E_END   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CTL_USE_INTERNAL_DMAC register field. */
#define ALT_SDMMC_CTL_USE_INTERNAL_DMAC_LSB        25
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CTL_USE_INTERNAL_DMAC register field. */
#define ALT_SDMMC_CTL_USE_INTERNAL_DMAC_MSB        25
/* The width in bits of the ALT_SDMMC_CTL_USE_INTERNAL_DMAC register field. */
#define ALT_SDMMC_CTL_USE_INTERNAL_DMAC_WIDTH      1
/* The mask used to set the ALT_SDMMC_CTL_USE_INTERNAL_DMAC register field value. */
#define ALT_SDMMC_CTL_USE_INTERNAL_DMAC_SET_MSK    0x02000000
/* The mask used to clear the ALT_SDMMC_CTL_USE_INTERNAL_DMAC register field value. */
#define ALT_SDMMC_CTL_USE_INTERNAL_DMAC_CLR_MSK    0xfdffffff
/* The reset value of the ALT_SDMMC_CTL_USE_INTERNAL_DMAC register field. */
#define ALT_SDMMC_CTL_USE_INTERNAL_DMAC_RESET      0x0
/* Extracts the ALT_SDMMC_CTL_USE_INTERNAL_DMAC field value from a register. */
#define ALT_SDMMC_CTL_USE_INTERNAL_DMAC_GET(value) (((value) & 0x02000000) >> 25)
/* Produces a ALT_SDMMC_CTL_USE_INTERNAL_DMAC register field value suitable for setting the register. */
#define ALT_SDMMC_CTL_USE_INTERNAL_DMAC_SET(value) (((value) << 25) & 0x02000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_CTL.
 */
struct ALT_SDMMC_CTL_s
{
    uint32_t  controller_reset              :  1;  /* Controller Reset */
    uint32_t  fifo_reset                    :  1;  /* FIFO Reset */
    uint32_t  dma_reset                     :  1;  /* Dma Reset */
    uint32_t                                :  1;  /* *UNDEFINED* */
    uint32_t  int_enable                    :  1;  /* Int Enable */
    uint32_t                                :  1;  /* *UNDEFINED* */
    uint32_t  read_wait                     :  1;  /* Read Wait */
    uint32_t  send_irq_response             :  1;  /* Send Irq Response */
    uint32_t  abort_read_data               :  1;  /* Abort Read Data */
    uint32_t  send_ccsd                     :  1;  /* Send CCSD */
    uint32_t  send_auto_stop_ccsd           :  1;  /* Send Auto Stop CCSD */
    uint32_t  ceata_device_interrupt_status :  1;  /* Ceata Device Interrupt Status */
    uint32_t                                : 13;  /* *UNDEFINED* */
    uint32_t  use_internal_dmac             :  1;  /* Use Internal DMAC */
    uint32_t                                :  6;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_CTL. */
typedef volatile struct ALT_SDMMC_CTL_s  ALT_SDMMC_CTL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_CTL register from the beginning of the component. */
#define ALT_SDMMC_CTL_OFST        0x0

/*
 * Register : Power Enable Register - pwren
 * 
 * Power on/off switch for card; once power is turned on, firmware should wait for
 * regulator/switch ramp-up time before trying to initialize card.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description 
 * :-------|:-------|:------|:-------------
 *  [0]    | RW     | 0x0   | Power Enable
 *  [31:1] | ???    | 0x0   | *UNDEFINED* 
 * 
 */
/*
 * Field : Power Enable - power_enable
 * 
 * Power on/off switch for one card; for example, bit[0] controls the card. Once
 * power is turned on, firmware should wait for regulator/switch ramp-up time
 * before trying to initialize card.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description
 * :-------------------------------|:------|:------------
 *  ALT_SDMMC_PWREN_POWER_EN_E_OFF | 0x0   | Power Off  
 *  ALT_SDMMC_PWREN_POWER_EN_E_ON  | 0x1   | Power On   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_PWREN_POWER_EN
 * 
 * Power Off
 */
#define ALT_SDMMC_PWREN_POWER_EN_E_OFF  0x0
/*
 * Enumerated value for register field ALT_SDMMC_PWREN_POWER_EN
 * 
 * Power On
 */
#define ALT_SDMMC_PWREN_POWER_EN_E_ON   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_PWREN_POWER_EN register field. */
#define ALT_SDMMC_PWREN_POWER_EN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_PWREN_POWER_EN register field. */
#define ALT_SDMMC_PWREN_POWER_EN_MSB        0
/* The width in bits of the ALT_SDMMC_PWREN_POWER_EN register field. */
#define ALT_SDMMC_PWREN_POWER_EN_WIDTH      1
/* The mask used to set the ALT_SDMMC_PWREN_POWER_EN register field value. */
#define ALT_SDMMC_PWREN_POWER_EN_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_PWREN_POWER_EN register field value. */
#define ALT_SDMMC_PWREN_POWER_EN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_PWREN_POWER_EN register field. */
#define ALT_SDMMC_PWREN_POWER_EN_RESET      0x0
/* Extracts the ALT_SDMMC_PWREN_POWER_EN field value from a register. */
#define ALT_SDMMC_PWREN_POWER_EN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_PWREN_POWER_EN register field value suitable for setting the register. */
#define ALT_SDMMC_PWREN_POWER_EN_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_PWREN.
 */
struct ALT_SDMMC_PWREN_s
{
    uint32_t  power_enable :  1;  /* Power Enable */
    uint32_t               : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_PWREN. */
typedef volatile struct ALT_SDMMC_PWREN_s  ALT_SDMMC_PWREN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_PWREN register from the beginning of the component. */
#define ALT_SDMMC_PWREN_OFST        0x4

/*
 * Register : Clock Divider Register - clkdiv
 * 
 * Divides Clock sdmmc_clk.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description  
 * :-------|:-------|:------|:--------------
 *  [7:0]  | RW     | 0x0   | Clk Divider 0
 *  [31:8] | ???    | 0x0   | *UNDEFINED*  
 * 
 */
/*
 * Field : Clk Divider 0 - clk_divider0
 * 
 * Clock divider-0 value. Clock division is 2*n. For example, value of 0 means
 * divide by 2*0 = 0 (no division, bypass), value of 1 means divide by 2*1 = 2,
 * value of ff means divide by 2*255 = 510, and so on.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CLKDIV_CLK_DIVR0 register field. */
#define ALT_SDMMC_CLKDIV_CLK_DIVR0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CLKDIV_CLK_DIVR0 register field. */
#define ALT_SDMMC_CLKDIV_CLK_DIVR0_MSB        7
/* The width in bits of the ALT_SDMMC_CLKDIV_CLK_DIVR0 register field. */
#define ALT_SDMMC_CLKDIV_CLK_DIVR0_WIDTH      8
/* The mask used to set the ALT_SDMMC_CLKDIV_CLK_DIVR0 register field value. */
#define ALT_SDMMC_CLKDIV_CLK_DIVR0_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SDMMC_CLKDIV_CLK_DIVR0 register field value. */
#define ALT_SDMMC_CLKDIV_CLK_DIVR0_CLR_MSK    0xffffff00
/* The reset value of the ALT_SDMMC_CLKDIV_CLK_DIVR0 register field. */
#define ALT_SDMMC_CLKDIV_CLK_DIVR0_RESET      0x0
/* Extracts the ALT_SDMMC_CLKDIV_CLK_DIVR0 field value from a register. */
#define ALT_SDMMC_CLKDIV_CLK_DIVR0_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SDMMC_CLKDIV_CLK_DIVR0 register field value suitable for setting the register. */
#define ALT_SDMMC_CLKDIV_CLK_DIVR0_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_CLKDIV.
 */
struct ALT_SDMMC_CLKDIV_s
{
    uint32_t  clk_divider0 :  8;  /* Clk Divider 0 */
    uint32_t               : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_CLKDIV. */
typedef volatile struct ALT_SDMMC_CLKDIV_s  ALT_SDMMC_CLKDIV_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_CLKDIV register from the beginning of the component. */
#define ALT_SDMMC_CLKDIV_OFST        0x8

/*
 * Register : SD Clock Source Register - clksrc
 * 
 * Selects among available clock dividers. The sdmmc_cclk_out is always from clock
 * divider 0.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description 
 * :-------|:-------|:------|:-------------
 *  [1:0]  | RW     | 0x0   | Clock Source
 *  [31:2] | ???    | 0x0   | *UNDEFINED* 
 * 
 */
/*
 * Field : Clock Source - clk_source
 * 
 * Selects among available clock dividers. The SD/MMC module is configured with
 * just one clock divider so this register should always be set to choose clkdiv0.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description    
 * :-----------------------------------|:------|:----------------
 *  ALT_SDMMC_CLKSRC_CLK_SRC_E_CLKDIV0 | 0x0   | Clock divider 0
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CLKSRC_CLK_SRC
 * 
 * Clock divider 0
 */
#define ALT_SDMMC_CLKSRC_CLK_SRC_E_CLKDIV0  0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CLKSRC_CLK_SRC register field. */
#define ALT_SDMMC_CLKSRC_CLK_SRC_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CLKSRC_CLK_SRC register field. */
#define ALT_SDMMC_CLKSRC_CLK_SRC_MSB        1
/* The width in bits of the ALT_SDMMC_CLKSRC_CLK_SRC register field. */
#define ALT_SDMMC_CLKSRC_CLK_SRC_WIDTH      2
/* The mask used to set the ALT_SDMMC_CLKSRC_CLK_SRC register field value. */
#define ALT_SDMMC_CLKSRC_CLK_SRC_SET_MSK    0x00000003
/* The mask used to clear the ALT_SDMMC_CLKSRC_CLK_SRC register field value. */
#define ALT_SDMMC_CLKSRC_CLK_SRC_CLR_MSK    0xfffffffc
/* The reset value of the ALT_SDMMC_CLKSRC_CLK_SRC register field. */
#define ALT_SDMMC_CLKSRC_CLK_SRC_RESET      0x0
/* Extracts the ALT_SDMMC_CLKSRC_CLK_SRC field value from a register. */
#define ALT_SDMMC_CLKSRC_CLK_SRC_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_SDMMC_CLKSRC_CLK_SRC register field value suitable for setting the register. */
#define ALT_SDMMC_CLKSRC_CLK_SRC_SET(value) (((value) << 0) & 0x00000003)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_CLKSRC.
 */
struct ALT_SDMMC_CLKSRC_s
{
    uint32_t  clk_source :  2;  /* Clock Source */
    uint32_t             : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_CLKSRC. */
typedef volatile struct ALT_SDMMC_CLKSRC_s  ALT_SDMMC_CLKSRC_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_CLKSRC register from the beginning of the component. */
#define ALT_SDMMC_CLKSRC_OFST        0xc

/*
 * Register : Clock Enable Register - clkena
 * 
 * Controls external SD/MMC Clock Enable.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description   
 * :--------|:-------|:------|:---------------
 *  [0]     | RW     | 0x0   | Cclk Enable   
 *  [15:1]  | ???    | 0x0   | *UNDEFINED*   
 *  [16]    | RW     | 0x0   | Cclk Low Power
 *  [31:17] | ???    | 0x0   | *UNDEFINED*   
 * 
 */
/*
 * Field : Cclk Enable - cclk_enable
 * 
 * Enables sdmmc_cclk_out.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description   
 * :--------------------------------|:------|:---------------
 *  ALT_SDMMC_CLKENA_CCLK_EN_E_DISD | 0x0   | SD/MMC Disable
 *  ALT_SDMMC_CLKENA_CCLK_EN_E_END  | 0x1   | SD/MMC Enable 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CLKENA_CCLK_EN
 * 
 * SD/MMC Disable
 */
#define ALT_SDMMC_CLKENA_CCLK_EN_E_DISD 0x0
/*
 * Enumerated value for register field ALT_SDMMC_CLKENA_CCLK_EN
 * 
 * SD/MMC Enable
 */
#define ALT_SDMMC_CLKENA_CCLK_EN_E_END  0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CLKENA_CCLK_EN register field. */
#define ALT_SDMMC_CLKENA_CCLK_EN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CLKENA_CCLK_EN register field. */
#define ALT_SDMMC_CLKENA_CCLK_EN_MSB        0
/* The width in bits of the ALT_SDMMC_CLKENA_CCLK_EN register field. */
#define ALT_SDMMC_CLKENA_CCLK_EN_WIDTH      1
/* The mask used to set the ALT_SDMMC_CLKENA_CCLK_EN register field value. */
#define ALT_SDMMC_CLKENA_CCLK_EN_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_CLKENA_CCLK_EN register field value. */
#define ALT_SDMMC_CLKENA_CCLK_EN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_CLKENA_CCLK_EN register field. */
#define ALT_SDMMC_CLKENA_CCLK_EN_RESET      0x0
/* Extracts the ALT_SDMMC_CLKENA_CCLK_EN field value from a register. */
#define ALT_SDMMC_CLKENA_CCLK_EN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_CLKENA_CCLK_EN register field value suitable for setting the register. */
#define ALT_SDMMC_CLKENA_CCLK_EN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Cclk Low Power - cclk_low_power
 * 
 * In low-power mode, stop sdmmc_cclk_out when card in IDLE (should be normally set
 * to only MMC and SD memory cards; for SDIO cards, if interrupts must be detected,
 * clock should not be stopped).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description       
 * :---------------------------------------|:------|:-------------------
 *  ALT_SDMMC_CLKENA_CCLK_LOW_POWER_E_DISD | 0x0   | Non-low-power mode
 *  ALT_SDMMC_CLKENA_CCLK_LOW_POWER_E_END  | 0x1   | Low-power mode    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CLKENA_CCLK_LOW_POWER
 * 
 * Non-low-power mode
 */
#define ALT_SDMMC_CLKENA_CCLK_LOW_POWER_E_DISD  0x0
/*
 * Enumerated value for register field ALT_SDMMC_CLKENA_CCLK_LOW_POWER
 * 
 * Low-power mode
 */
#define ALT_SDMMC_CLKENA_CCLK_LOW_POWER_E_END   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CLKENA_CCLK_LOW_POWER register field. */
#define ALT_SDMMC_CLKENA_CCLK_LOW_POWER_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CLKENA_CCLK_LOW_POWER register field. */
#define ALT_SDMMC_CLKENA_CCLK_LOW_POWER_MSB        16
/* The width in bits of the ALT_SDMMC_CLKENA_CCLK_LOW_POWER register field. */
#define ALT_SDMMC_CLKENA_CCLK_LOW_POWER_WIDTH      1
/* The mask used to set the ALT_SDMMC_CLKENA_CCLK_LOW_POWER register field value. */
#define ALT_SDMMC_CLKENA_CCLK_LOW_POWER_SET_MSK    0x00010000
/* The mask used to clear the ALT_SDMMC_CLKENA_CCLK_LOW_POWER register field value. */
#define ALT_SDMMC_CLKENA_CCLK_LOW_POWER_CLR_MSK    0xfffeffff
/* The reset value of the ALT_SDMMC_CLKENA_CCLK_LOW_POWER register field. */
#define ALT_SDMMC_CLKENA_CCLK_LOW_POWER_RESET      0x0
/* Extracts the ALT_SDMMC_CLKENA_CCLK_LOW_POWER field value from a register. */
#define ALT_SDMMC_CLKENA_CCLK_LOW_POWER_GET(value) (((value) & 0x00010000) >> 16)
/* Produces a ALT_SDMMC_CLKENA_CCLK_LOW_POWER register field value suitable for setting the register. */
#define ALT_SDMMC_CLKENA_CCLK_LOW_POWER_SET(value) (((value) << 16) & 0x00010000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_CLKENA.
 */
struct ALT_SDMMC_CLKENA_s
{
    uint32_t  cclk_enable    :  1;  /* Cclk Enable */
    uint32_t                 : 15;  /* *UNDEFINED* */
    uint32_t  cclk_low_power :  1;  /* Cclk Low Power */
    uint32_t                 : 15;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_CLKENA. */
typedef volatile struct ALT_SDMMC_CLKENA_s  ALT_SDMMC_CLKENA_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_CLKENA register from the beginning of the component. */
#define ALT_SDMMC_CLKENA_OFST        0x10

/*
 * Register : Timeout Register - tmout
 * 
 * Sets timeout values
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset    | Description     
 * :-------|:-------|:---------|:-----------------
 *  [7:0]  | RW     | 0x40     | Response Timeout
 *  [31:8] | RW     | 0xffffff | Data Timeout    
 * 
 */
/*
 * Field : Response Timeout - response_timeout
 * 
 * Response timeout value. Value is in number of card output clocks sdmmc_cclk_out.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_TMOUT_RESPONSE_TMO register field. */
#define ALT_SDMMC_TMOUT_RESPONSE_TMO_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_TMOUT_RESPONSE_TMO register field. */
#define ALT_SDMMC_TMOUT_RESPONSE_TMO_MSB        7
/* The width in bits of the ALT_SDMMC_TMOUT_RESPONSE_TMO register field. */
#define ALT_SDMMC_TMOUT_RESPONSE_TMO_WIDTH      8
/* The mask used to set the ALT_SDMMC_TMOUT_RESPONSE_TMO register field value. */
#define ALT_SDMMC_TMOUT_RESPONSE_TMO_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SDMMC_TMOUT_RESPONSE_TMO register field value. */
#define ALT_SDMMC_TMOUT_RESPONSE_TMO_CLR_MSK    0xffffff00
/* The reset value of the ALT_SDMMC_TMOUT_RESPONSE_TMO register field. */
#define ALT_SDMMC_TMOUT_RESPONSE_TMO_RESET      0x40
/* Extracts the ALT_SDMMC_TMOUT_RESPONSE_TMO field value from a register. */
#define ALT_SDMMC_TMOUT_RESPONSE_TMO_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SDMMC_TMOUT_RESPONSE_TMO register field value suitable for setting the register. */
#define ALT_SDMMC_TMOUT_RESPONSE_TMO_SET(value) (((value) << 0) & 0x000000ff)

/*
 * Field : Data Timeout - data_timeout
 * 
 * Value for card Data Read Timeout; same value also used for Data Starvation by
 * Host timeout. Value is in number of card output clocks sdmmc_cclk_out of
 * selected card.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_TMOUT_DATA_TMO register field. */
#define ALT_SDMMC_TMOUT_DATA_TMO_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_TMOUT_DATA_TMO register field. */
#define ALT_SDMMC_TMOUT_DATA_TMO_MSB        31
/* The width in bits of the ALT_SDMMC_TMOUT_DATA_TMO register field. */
#define ALT_SDMMC_TMOUT_DATA_TMO_WIDTH      24
/* The mask used to set the ALT_SDMMC_TMOUT_DATA_TMO register field value. */
#define ALT_SDMMC_TMOUT_DATA_TMO_SET_MSK    0xffffff00
/* The mask used to clear the ALT_SDMMC_TMOUT_DATA_TMO register field value. */
#define ALT_SDMMC_TMOUT_DATA_TMO_CLR_MSK    0x000000ff
/* The reset value of the ALT_SDMMC_TMOUT_DATA_TMO register field. */
#define ALT_SDMMC_TMOUT_DATA_TMO_RESET      0xffffff
/* Extracts the ALT_SDMMC_TMOUT_DATA_TMO field value from a register. */
#define ALT_SDMMC_TMOUT_DATA_TMO_GET(value) (((value) & 0xffffff00) >> 8)
/* Produces a ALT_SDMMC_TMOUT_DATA_TMO register field value suitable for setting the register. */
#define ALT_SDMMC_TMOUT_DATA_TMO_SET(value) (((value) << 8) & 0xffffff00)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_TMOUT.
 */
struct ALT_SDMMC_TMOUT_s
{
    uint32_t  response_timeout :  8;  /* Response Timeout */
    uint32_t  data_timeout     : 24;  /* Data Timeout */
};

/* The typedef declaration for register ALT_SDMMC_TMOUT. */
typedef volatile struct ALT_SDMMC_TMOUT_s  ALT_SDMMC_TMOUT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_TMOUT register from the beginning of the component. */
#define ALT_SDMMC_TMOUT_OFST        0x14

/*
 * Register : Card Type Register - ctype
 * 
 * Describes card formats.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description           
 * :--------|:-------|:------|:-----------------------
 *  [0]     | RW     | 0x0   | Card Width 1 or 4 Bits
 *  [15:1]  | ???    | 0x0   | *UNDEFINED*           
 *  [16]    | RW     | 0x0   | Card Width 8 Bit      
 *  [31:17] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : Card Width 1 or 4 Bits - card_width2
 * 
 * Ignored if card_width1 is MODE8BIT.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description
 * :--------------------------------------|:------|:------------
 *  ALT_SDMMC_CTYPE_CARD_WIDTH2_E_MOD1BIT | 0x0   | 1-bit mode 
 *  ALT_SDMMC_CTYPE_CARD_WIDTH2_E_MOD4BIT | 0x1   | 4-bit mode 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CTYPE_CARD_WIDTH2
 * 
 * 1-bit mode
 */
#define ALT_SDMMC_CTYPE_CARD_WIDTH2_E_MOD1BIT   0x0
/*
 * Enumerated value for register field ALT_SDMMC_CTYPE_CARD_WIDTH2
 * 
 * 4-bit mode
 */
#define ALT_SDMMC_CTYPE_CARD_WIDTH2_E_MOD4BIT   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CTYPE_CARD_WIDTH2 register field. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH2_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CTYPE_CARD_WIDTH2 register field. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH2_MSB        0
/* The width in bits of the ALT_SDMMC_CTYPE_CARD_WIDTH2 register field. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH2_WIDTH      1
/* The mask used to set the ALT_SDMMC_CTYPE_CARD_WIDTH2 register field value. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH2_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_CTYPE_CARD_WIDTH2 register field value. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH2_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_CTYPE_CARD_WIDTH2 register field. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH2_RESET      0x0
/* Extracts the ALT_SDMMC_CTYPE_CARD_WIDTH2 field value from a register. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH2_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_CTYPE_CARD_WIDTH2 register field value suitable for setting the register. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH2_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Card Width 8 Bit - card_width1
 * 
 * Indicates if card is 8 bit or othersize. If not 8-bit, card_width2 specifies the
 * width.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description   
 * :--------------------------------------|:------|:---------------
 *  ALT_SDMMC_CTYPE_CARD_WIDTH1_E_NON8BIT | 0x0   | Non 8-bit mode
 *  ALT_SDMMC_CTYPE_CARD_WIDTH1_E_MOD8BIT | 0x1   | 8-bit mode    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CTYPE_CARD_WIDTH1
 * 
 * Non 8-bit mode
 */
#define ALT_SDMMC_CTYPE_CARD_WIDTH1_E_NON8BIT   0x0
/*
 * Enumerated value for register field ALT_SDMMC_CTYPE_CARD_WIDTH1
 * 
 * 8-bit mode
 */
#define ALT_SDMMC_CTYPE_CARD_WIDTH1_E_MOD8BIT   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CTYPE_CARD_WIDTH1 register field. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH1_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CTYPE_CARD_WIDTH1 register field. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH1_MSB        16
/* The width in bits of the ALT_SDMMC_CTYPE_CARD_WIDTH1 register field. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH1_WIDTH      1
/* The mask used to set the ALT_SDMMC_CTYPE_CARD_WIDTH1 register field value. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH1_SET_MSK    0x00010000
/* The mask used to clear the ALT_SDMMC_CTYPE_CARD_WIDTH1 register field value. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH1_CLR_MSK    0xfffeffff
/* The reset value of the ALT_SDMMC_CTYPE_CARD_WIDTH1 register field. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH1_RESET      0x0
/* Extracts the ALT_SDMMC_CTYPE_CARD_WIDTH1 field value from a register. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH1_GET(value) (((value) & 0x00010000) >> 16)
/* Produces a ALT_SDMMC_CTYPE_CARD_WIDTH1 register field value suitable for setting the register. */
#define ALT_SDMMC_CTYPE_CARD_WIDTH1_SET(value) (((value) << 16) & 0x00010000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_CTYPE.
 */
struct ALT_SDMMC_CTYPE_s
{
    uint32_t  card_width2 :  1;  /* Card Width 1 or 4 Bits */
    uint32_t              : 15;  /* *UNDEFINED* */
    uint32_t  card_width1 :  1;  /* Card Width 8 Bit */
    uint32_t              : 15;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_CTYPE. */
typedef volatile struct ALT_SDMMC_CTYPE_s  ALT_SDMMC_CTYPE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_CTYPE register from the beginning of the component. */
#define ALT_SDMMC_CTYPE_OFST        0x18

/*
 * Register : Block Size Register - blksiz
 * 
 * The Block Size.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description
 * :--------|:-------|:------|:------------
 *  [15:0]  | RW     | 0x200 | Block Size 
 *  [31:16] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Block Size - block_size
 * 
 * The size of a block in bytes.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_BLKSIZ_BLOCK_SIZE register field. */
#define ALT_SDMMC_BLKSIZ_BLOCK_SIZE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_BLKSIZ_BLOCK_SIZE register field. */
#define ALT_SDMMC_BLKSIZ_BLOCK_SIZE_MSB        15
/* The width in bits of the ALT_SDMMC_BLKSIZ_BLOCK_SIZE register field. */
#define ALT_SDMMC_BLKSIZ_BLOCK_SIZE_WIDTH      16
/* The mask used to set the ALT_SDMMC_BLKSIZ_BLOCK_SIZE register field value. */
#define ALT_SDMMC_BLKSIZ_BLOCK_SIZE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_SDMMC_BLKSIZ_BLOCK_SIZE register field value. */
#define ALT_SDMMC_BLKSIZ_BLOCK_SIZE_CLR_MSK    0xffff0000
/* The reset value of the ALT_SDMMC_BLKSIZ_BLOCK_SIZE register field. */
#define ALT_SDMMC_BLKSIZ_BLOCK_SIZE_RESET      0x200
/* Extracts the ALT_SDMMC_BLKSIZ_BLOCK_SIZE field value from a register. */
#define ALT_SDMMC_BLKSIZ_BLOCK_SIZE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_SDMMC_BLKSIZ_BLOCK_SIZE register field value suitable for setting the register. */
#define ALT_SDMMC_BLKSIZ_BLOCK_SIZE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_BLKSIZ.
 */
struct ALT_SDMMC_BLKSIZ_s
{
    uint32_t  block_size : 16;  /* Block Size */
    uint32_t             : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_BLKSIZ. */
typedef volatile struct ALT_SDMMC_BLKSIZ_s  ALT_SDMMC_BLKSIZ_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_BLKSIZ register from the beginning of the component. */
#define ALT_SDMMC_BLKSIZ_OFST        0x1c

/*
 * Register : Byte Count Register - bytcnt
 * 
 * The number of bytes to be transferred.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [31:0] | RW     | 0x200 | Byte Count 
 * 
 */
/*
 * Field : Byte Count - byte_count
 * 
 * This value should be an integer multiple of the Block Size for block transfers.
 * For undefined number of byte transfers, byte count should be set to 0. When byte
 * count is set to 0, it is responsibility of host to explicitly send stop/abort
 * command to terminate data transfer.
 * 
 * Note: In SDIO mode, if a single transfer is greater than 4 bytes and non-DWORD-
 * aligned, the transfer should be broken where only the last transfer is non-
 * DWORD-aligned and less than 4 bytes. For example, if a transfer of 129 bytes
 * must occur, then the driver should start at least two transfers; one with 128
 * bytes and the other with 1 byte.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_BYTCNT_BYTE_COUNT register field. */
#define ALT_SDMMC_BYTCNT_BYTE_COUNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_BYTCNT_BYTE_COUNT register field. */
#define ALT_SDMMC_BYTCNT_BYTE_COUNT_MSB        31
/* The width in bits of the ALT_SDMMC_BYTCNT_BYTE_COUNT register field. */
#define ALT_SDMMC_BYTCNT_BYTE_COUNT_WIDTH      32
/* The mask used to set the ALT_SDMMC_BYTCNT_BYTE_COUNT register field value. */
#define ALT_SDMMC_BYTCNT_BYTE_COUNT_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDMMC_BYTCNT_BYTE_COUNT register field value. */
#define ALT_SDMMC_BYTCNT_BYTE_COUNT_CLR_MSK    0x00000000
/* The reset value of the ALT_SDMMC_BYTCNT_BYTE_COUNT register field. */
#define ALT_SDMMC_BYTCNT_BYTE_COUNT_RESET      0x200
/* Extracts the ALT_SDMMC_BYTCNT_BYTE_COUNT field value from a register. */
#define ALT_SDMMC_BYTCNT_BYTE_COUNT_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDMMC_BYTCNT_BYTE_COUNT register field value suitable for setting the register. */
#define ALT_SDMMC_BYTCNT_BYTE_COUNT_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_BYTCNT.
 */
struct ALT_SDMMC_BYTCNT_s
{
    uint32_t  byte_count : 32;  /* Byte Count */
};

/* The typedef declaration for register ALT_SDMMC_BYTCNT. */
typedef volatile struct ALT_SDMMC_BYTCNT_s  ALT_SDMMC_BYTCNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_BYTCNT register from the beginning of the component. */
#define ALT_SDMMC_BYTCNT_OFST        0x20

/*
 * Register : Interrupt Mask Register - intmask
 * 
 * Allows Masking of Various Interrupts
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                    
 * :--------|:-------|:------|:--------------------------------
 *  [0]     | RW     | 0x0   | Card Detected                  
 *  [1]     | RW     | 0x0   | Response Error                 
 *  [2]     | RW     | 0x0   | Command Done                   
 *  [3]     | RW     | 0x0   | Data Transfer Over             
 *  [4]     | RW     | 0x0   | Transmit FIFO Data Request     
 *  [5]     | RW     | 0x0   | Receive FIFO Data Request (    
 *  [6]     | RW     | 0x0   | Response CRC Error             
 *  [7]     | RW     | 0x0   | Data CRC Error                 
 *  [8]     | RW     | 0x0   | Response Timeout               
 *  [9]     | RW     | 0x0   | Data Read Timeout              
 *  [10]    | RW     | 0x0   | Data Starvation  Host Timeout  
 *  [11]    | RW     | 0x0   | FIFO Underrun Overrun Error    
 *  [12]    | RW     | 0x0   | Hardware Locked Write Error    
 *  [13]    | RW     | 0x0   | Start-bit Error                
 *  [14]    | RW     | 0x0   | Auto Command Done              
 *  [15]    | RW     | 0x0   | End-bit Error Read Write no CRC
 *  [16]    | RW     | 0x0   | SDIO Interrupt Mask            
 *  [31:17] | ???    | 0x0   | *UNDEFINED*                    
 * 
 */
/*
 * Field : Card Detected - cd
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description        
 * :----------------------------|:------|:--------------------
 *  ALT_SDMMC_INTMSK_CD_E_MSK   | 0x0   | Card Detected Mask 
 *  ALT_SDMMC_INTMSK_CD_E_NOMSK | 0x1   | Card Detect No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_CD
 * 
 * Card Detected Mask
 */
#define ALT_SDMMC_INTMSK_CD_E_MSK   0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_CD
 * 
 * Card Detect No Mask
 */
#define ALT_SDMMC_INTMSK_CD_E_NOMSK 0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_CD register field. */
#define ALT_SDMMC_INTMSK_CD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_CD register field. */
#define ALT_SDMMC_INTMSK_CD_MSB        0
/* The width in bits of the ALT_SDMMC_INTMSK_CD register field. */
#define ALT_SDMMC_INTMSK_CD_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_CD register field value. */
#define ALT_SDMMC_INTMSK_CD_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_INTMSK_CD register field value. */
#define ALT_SDMMC_INTMSK_CD_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_INTMSK_CD register field. */
#define ALT_SDMMC_INTMSK_CD_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_CD field value from a register. */
#define ALT_SDMMC_INTMSK_CD_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_INTMSK_CD register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_CD_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Response Error - re
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description           
 * :----------------------------|:------|:-----------------------
 *  ALT_SDMMC_INTMSK_RE_E_MSK   | 0x0   | Response error Mask   
 *  ALT_SDMMC_INTMSK_RE_E_NOMSK | 0x1   | Response error No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_RE
 * 
 * Response error Mask
 */
#define ALT_SDMMC_INTMSK_RE_E_MSK   0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_RE
 * 
 * Response error No Mask
 */
#define ALT_SDMMC_INTMSK_RE_E_NOMSK 0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_RE register field. */
#define ALT_SDMMC_INTMSK_RE_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_RE register field. */
#define ALT_SDMMC_INTMSK_RE_MSB        1
/* The width in bits of the ALT_SDMMC_INTMSK_RE register field. */
#define ALT_SDMMC_INTMSK_RE_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_RE register field value. */
#define ALT_SDMMC_INTMSK_RE_SET_MSK    0x00000002
/* The mask used to clear the ALT_SDMMC_INTMSK_RE register field value. */
#define ALT_SDMMC_INTMSK_RE_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SDMMC_INTMSK_RE register field. */
#define ALT_SDMMC_INTMSK_RE_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_RE field value from a register. */
#define ALT_SDMMC_INTMSK_RE_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SDMMC_INTMSK_RE register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_RE_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Command Done - cmd
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description         
 * :-----------------------------|:------|:---------------------
 *  ALT_SDMMC_INTMSK_CMD_E_MSK   | 0x0   | Command Done Mask   
 *  ALT_SDMMC_INTMSK_CMD_E_NOMSK | 0x1   | Command Done No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_CMD
 * 
 * Command Done Mask
 */
#define ALT_SDMMC_INTMSK_CMD_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_CMD
 * 
 * Command Done No Mask
 */
#define ALT_SDMMC_INTMSK_CMD_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_CMD register field. */
#define ALT_SDMMC_INTMSK_CMD_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_CMD register field. */
#define ALT_SDMMC_INTMSK_CMD_MSB        2
/* The width in bits of the ALT_SDMMC_INTMSK_CMD register field. */
#define ALT_SDMMC_INTMSK_CMD_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_CMD register field value. */
#define ALT_SDMMC_INTMSK_CMD_SET_MSK    0x00000004
/* The mask used to clear the ALT_SDMMC_INTMSK_CMD register field value. */
#define ALT_SDMMC_INTMSK_CMD_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SDMMC_INTMSK_CMD register field. */
#define ALT_SDMMC_INTMSK_CMD_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_CMD field value from a register. */
#define ALT_SDMMC_INTMSK_CMD_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SDMMC_INTMSK_CMD register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_CMD_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Data Transfer Over - dto
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description               
 * :-----------------------------|:------|:---------------------------
 *  ALT_SDMMC_INTMSK_DTO_E_MSK   | 0x0   | Data transfer over Mask   
 *  ALT_SDMMC_INTMSK_DTO_E_NOMSK | 0x1   | Data transfer over No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_DTO
 * 
 * Data transfer over Mask
 */
#define ALT_SDMMC_INTMSK_DTO_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_DTO
 * 
 * Data transfer over No Mask
 */
#define ALT_SDMMC_INTMSK_DTO_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_DTO register field. */
#define ALT_SDMMC_INTMSK_DTO_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_DTO register field. */
#define ALT_SDMMC_INTMSK_DTO_MSB        3
/* The width in bits of the ALT_SDMMC_INTMSK_DTO register field. */
#define ALT_SDMMC_INTMSK_DTO_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_DTO register field value. */
#define ALT_SDMMC_INTMSK_DTO_SET_MSK    0x00000008
/* The mask used to clear the ALT_SDMMC_INTMSK_DTO register field value. */
#define ALT_SDMMC_INTMSK_DTO_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SDMMC_INTMSK_DTO register field. */
#define ALT_SDMMC_INTMSK_DTO_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_DTO field value from a register. */
#define ALT_SDMMC_INTMSK_DTO_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SDMMC_INTMSK_DTO register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_DTO_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Transmit FIFO Data Request - txdr
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                       
 * :------------------------------|:------|:-----------------------------------
 *  ALT_SDMMC_INTMSK_TXDR_E_MSK   | 0x0   | Transmit FIFO data request Mask   
 *  ALT_SDMMC_INTMSK_TXDR_E_NOMSK | 0x1   | Transmit FIFO data request No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_TXDR
 * 
 * Transmit FIFO data request Mask
 */
#define ALT_SDMMC_INTMSK_TXDR_E_MSK     0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_TXDR
 * 
 * Transmit FIFO data request No Mask
 */
#define ALT_SDMMC_INTMSK_TXDR_E_NOMSK   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_TXDR register field. */
#define ALT_SDMMC_INTMSK_TXDR_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_TXDR register field. */
#define ALT_SDMMC_INTMSK_TXDR_MSB        4
/* The width in bits of the ALT_SDMMC_INTMSK_TXDR register field. */
#define ALT_SDMMC_INTMSK_TXDR_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_TXDR register field value. */
#define ALT_SDMMC_INTMSK_TXDR_SET_MSK    0x00000010
/* The mask used to clear the ALT_SDMMC_INTMSK_TXDR register field value. */
#define ALT_SDMMC_INTMSK_TXDR_CLR_MSK    0xffffffef
/* The reset value of the ALT_SDMMC_INTMSK_TXDR register field. */
#define ALT_SDMMC_INTMSK_TXDR_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_TXDR field value from a register. */
#define ALT_SDMMC_INTMSK_TXDR_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SDMMC_INTMSK_TXDR register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_TXDR_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Receive FIFO Data Request ( - rxdr
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                      
 * :------------------------------|:------|:----------------------------------
 *  ALT_SDMMC_INTMSK_RXDR_E_MSK   | 0x0   | Receive FIFO data request Mask   
 *  ALT_SDMMC_INTMSK_RXDR_E_NOMSK | 0x1   | Receive FIFO data request No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_RXDR
 * 
 * Receive FIFO data request Mask
 */
#define ALT_SDMMC_INTMSK_RXDR_E_MSK     0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_RXDR
 * 
 * Receive FIFO data request No Mask
 */
#define ALT_SDMMC_INTMSK_RXDR_E_NOMSK   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_RXDR register field. */
#define ALT_SDMMC_INTMSK_RXDR_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_RXDR register field. */
#define ALT_SDMMC_INTMSK_RXDR_MSB        5
/* The width in bits of the ALT_SDMMC_INTMSK_RXDR register field. */
#define ALT_SDMMC_INTMSK_RXDR_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_RXDR register field value. */
#define ALT_SDMMC_INTMSK_RXDR_SET_MSK    0x00000020
/* The mask used to clear the ALT_SDMMC_INTMSK_RXDR register field value. */
#define ALT_SDMMC_INTMSK_RXDR_CLR_MSK    0xffffffdf
/* The reset value of the ALT_SDMMC_INTMSK_RXDR register field. */
#define ALT_SDMMC_INTMSK_RXDR_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_RXDR field value from a register. */
#define ALT_SDMMC_INTMSK_RXDR_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_SDMMC_INTMSK_RXDR register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_RXDR_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Response CRC Error - rcrc
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description               
 * :------------------------------|:------|:---------------------------
 *  ALT_SDMMC_INTMSK_RCRC_E_MSK   | 0x0   | Response CRC error Mask   
 *  ALT_SDMMC_INTMSK_RCRC_E_NOMSK | 0x1   | Response CRC error No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_RCRC
 * 
 * Response CRC error Mask
 */
#define ALT_SDMMC_INTMSK_RCRC_E_MSK     0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_RCRC
 * 
 * Response CRC error No Mask
 */
#define ALT_SDMMC_INTMSK_RCRC_E_NOMSK   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_RCRC register field. */
#define ALT_SDMMC_INTMSK_RCRC_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_RCRC register field. */
#define ALT_SDMMC_INTMSK_RCRC_MSB        6
/* The width in bits of the ALT_SDMMC_INTMSK_RCRC register field. */
#define ALT_SDMMC_INTMSK_RCRC_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_RCRC register field value. */
#define ALT_SDMMC_INTMSK_RCRC_SET_MSK    0x00000040
/* The mask used to clear the ALT_SDMMC_INTMSK_RCRC register field value. */
#define ALT_SDMMC_INTMSK_RCRC_CLR_MSK    0xffffffbf
/* The reset value of the ALT_SDMMC_INTMSK_RCRC register field. */
#define ALT_SDMMC_INTMSK_RCRC_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_RCRC field value from a register. */
#define ALT_SDMMC_INTMSK_RCRC_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_SDMMC_INTMSK_RCRC register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_RCRC_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Data CRC Error - dcrc
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description           
 * :------------------------------|:------|:-----------------------
 *  ALT_SDMMC_INTMSK_DCRC_E_MSK   | 0x0   | Data CRC error Mask   
 *  ALT_SDMMC_INTMSK_DCRC_E_NOMSK | 0x1   | Data CRC error No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_DCRC
 * 
 * Data CRC error Mask
 */
#define ALT_SDMMC_INTMSK_DCRC_E_MSK     0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_DCRC
 * 
 * Data CRC error No Mask
 */
#define ALT_SDMMC_INTMSK_DCRC_E_NOMSK   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_DCRC register field. */
#define ALT_SDMMC_INTMSK_DCRC_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_DCRC register field. */
#define ALT_SDMMC_INTMSK_DCRC_MSB        7
/* The width in bits of the ALT_SDMMC_INTMSK_DCRC register field. */
#define ALT_SDMMC_INTMSK_DCRC_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_DCRC register field value. */
#define ALT_SDMMC_INTMSK_DCRC_SET_MSK    0x00000080
/* The mask used to clear the ALT_SDMMC_INTMSK_DCRC register field value. */
#define ALT_SDMMC_INTMSK_DCRC_CLR_MSK    0xffffff7f
/* The reset value of the ALT_SDMMC_INTMSK_DCRC register field. */
#define ALT_SDMMC_INTMSK_DCRC_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_DCRC field value from a register. */
#define ALT_SDMMC_INTMSK_DCRC_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_SDMMC_INTMSK_DCRC register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_DCRC_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Response Timeout - rto
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description             
 * :-----------------------------|:------|:-------------------------
 *  ALT_SDMMC_INTMSK_RTO_E_MSK   | 0x0   | Response timeout Mask   
 *  ALT_SDMMC_INTMSK_RTO_E_NOMSK | 0x1   | Response timeout No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_RTO
 * 
 * Response timeout Mask
 */
#define ALT_SDMMC_INTMSK_RTO_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_RTO
 * 
 * Response timeout No Mask
 */
#define ALT_SDMMC_INTMSK_RTO_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_RTO register field. */
#define ALT_SDMMC_INTMSK_RTO_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_RTO register field. */
#define ALT_SDMMC_INTMSK_RTO_MSB        8
/* The width in bits of the ALT_SDMMC_INTMSK_RTO register field. */
#define ALT_SDMMC_INTMSK_RTO_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_RTO register field value. */
#define ALT_SDMMC_INTMSK_RTO_SET_MSK    0x00000100
/* The mask used to clear the ALT_SDMMC_INTMSK_RTO register field value. */
#define ALT_SDMMC_INTMSK_RTO_CLR_MSK    0xfffffeff
/* The reset value of the ALT_SDMMC_INTMSK_RTO register field. */
#define ALT_SDMMC_INTMSK_RTO_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_RTO field value from a register. */
#define ALT_SDMMC_INTMSK_RTO_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_SDMMC_INTMSK_RTO register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_RTO_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Data Read Timeout - drt
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description              
 * :-----------------------------|:------|:--------------------------
 *  ALT_SDMMC_INTMSK_DRT_E_MSK   | 0x0   | Data read timeout Mask   
 *  ALT_SDMMC_INTMSK_DRT_E_NOMSK | 0x1   | Data read timeout No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_DRT
 * 
 * Data read timeout Mask
 */
#define ALT_SDMMC_INTMSK_DRT_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_DRT
 * 
 * Data read timeout No Mask
 */
#define ALT_SDMMC_INTMSK_DRT_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_DRT register field. */
#define ALT_SDMMC_INTMSK_DRT_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_DRT register field. */
#define ALT_SDMMC_INTMSK_DRT_MSB        9
/* The width in bits of the ALT_SDMMC_INTMSK_DRT register field. */
#define ALT_SDMMC_INTMSK_DRT_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_DRT register field value. */
#define ALT_SDMMC_INTMSK_DRT_SET_MSK    0x00000200
/* The mask used to clear the ALT_SDMMC_INTMSK_DRT register field value. */
#define ALT_SDMMC_INTMSK_DRT_CLR_MSK    0xfffffdff
/* The reset value of the ALT_SDMMC_INTMSK_DRT register field. */
#define ALT_SDMMC_INTMSK_DRT_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_DRT field value from a register. */
#define ALT_SDMMC_INTMSK_DRT_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_SDMMC_INTMSK_DRT register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_DRT_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Data Starvation  Host Timeout - hto
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description                            
 * :-----------------------------|:------|:----------------------------------------
 *  ALT_SDMMC_INTMSK_HTO_E_MSK   | 0x0   | Data starvation by host timeout Mask   
 *  ALT_SDMMC_INTMSK_HTO_E_NOMSK | 0x1   | Data starvation by host timeout No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_HTO
 * 
 * Data starvation by host timeout Mask
 */
#define ALT_SDMMC_INTMSK_HTO_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_HTO
 * 
 * Data starvation by host timeout No Mask
 */
#define ALT_SDMMC_INTMSK_HTO_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_HTO register field. */
#define ALT_SDMMC_INTMSK_HTO_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_HTO register field. */
#define ALT_SDMMC_INTMSK_HTO_MSB        10
/* The width in bits of the ALT_SDMMC_INTMSK_HTO register field. */
#define ALT_SDMMC_INTMSK_HTO_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_HTO register field value. */
#define ALT_SDMMC_INTMSK_HTO_SET_MSK    0x00000400
/* The mask used to clear the ALT_SDMMC_INTMSK_HTO register field value. */
#define ALT_SDMMC_INTMSK_HTO_CLR_MSK    0xfffffbff
/* The reset value of the ALT_SDMMC_INTMSK_HTO register field. */
#define ALT_SDMMC_INTMSK_HTO_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_HTO field value from a register. */
#define ALT_SDMMC_INTMSK_HTO_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_SDMMC_INTMSK_HTO register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_HTO_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : FIFO Underrun Overrun Error - frun
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                        
 * :------------------------------|:------|:------------------------------------
 *  ALT_SDMMC_INTMSK_FRUN_E_MSK   | 0x0   | FIFO underrun/overrun error Mask   
 *  ALT_SDMMC_INTMSK_FRUN_E_NOMSK | 0x1   | FIFO underrun/overrun error No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_FRUN
 * 
 * FIFO underrun/overrun error Mask
 */
#define ALT_SDMMC_INTMSK_FRUN_E_MSK     0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_FRUN
 * 
 * FIFO underrun/overrun error No Mask
 */
#define ALT_SDMMC_INTMSK_FRUN_E_NOMSK   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_FRUN register field. */
#define ALT_SDMMC_INTMSK_FRUN_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_FRUN register field. */
#define ALT_SDMMC_INTMSK_FRUN_MSB        11
/* The width in bits of the ALT_SDMMC_INTMSK_FRUN register field. */
#define ALT_SDMMC_INTMSK_FRUN_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_FRUN register field value. */
#define ALT_SDMMC_INTMSK_FRUN_SET_MSK    0x00000800
/* The mask used to clear the ALT_SDMMC_INTMSK_FRUN register field value. */
#define ALT_SDMMC_INTMSK_FRUN_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_SDMMC_INTMSK_FRUN register field. */
#define ALT_SDMMC_INTMSK_FRUN_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_FRUN field value from a register. */
#define ALT_SDMMC_INTMSK_FRUN_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_SDMMC_INTMSK_FRUN register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_FRUN_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : Hardware Locked Write Error - hle
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description                        
 * :-----------------------------|:------|:------------------------------------
 *  ALT_SDMMC_INTMSK_HLE_E_MSK   | 0x0   | Hardware locked write error Mask   
 *  ALT_SDMMC_INTMSK_HLE_E_NOMSK | 0x1   | Hardware locked write error No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_HLE
 * 
 * Hardware locked write error Mask
 */
#define ALT_SDMMC_INTMSK_HLE_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_HLE
 * 
 * Hardware locked write error No Mask
 */
#define ALT_SDMMC_INTMSK_HLE_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_HLE register field. */
#define ALT_SDMMC_INTMSK_HLE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_HLE register field. */
#define ALT_SDMMC_INTMSK_HLE_MSB        12
/* The width in bits of the ALT_SDMMC_INTMSK_HLE register field. */
#define ALT_SDMMC_INTMSK_HLE_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_HLE register field value. */
#define ALT_SDMMC_INTMSK_HLE_SET_MSK    0x00001000
/* The mask used to clear the ALT_SDMMC_INTMSK_HLE register field value. */
#define ALT_SDMMC_INTMSK_HLE_CLR_MSK    0xffffefff
/* The reset value of the ALT_SDMMC_INTMSK_HLE register field. */
#define ALT_SDMMC_INTMSK_HLE_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_HLE field value from a register. */
#define ALT_SDMMC_INTMSK_HLE_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_SDMMC_INTMSK_HLE register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_HLE_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : Start-bit Error - sbe
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description            
 * :-----------------------------|:------|:------------------------
 *  ALT_SDMMC_INTMSK_SBE_E_MSK   | 0x0   | Start-bit error Mask   
 *  ALT_SDMMC_INTMSK_SBE_E_NOMSK | 0x1   | Start-bit error No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_SBE
 * 
 * Start-bit error Mask
 */
#define ALT_SDMMC_INTMSK_SBE_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_SBE
 * 
 * Start-bit error No Mask
 */
#define ALT_SDMMC_INTMSK_SBE_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_SBE register field. */
#define ALT_SDMMC_INTMSK_SBE_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_SBE register field. */
#define ALT_SDMMC_INTMSK_SBE_MSB        13
/* The width in bits of the ALT_SDMMC_INTMSK_SBE register field. */
#define ALT_SDMMC_INTMSK_SBE_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_SBE register field value. */
#define ALT_SDMMC_INTMSK_SBE_SET_MSK    0x00002000
/* The mask used to clear the ALT_SDMMC_INTMSK_SBE register field value. */
#define ALT_SDMMC_INTMSK_SBE_CLR_MSK    0xffffdfff
/* The reset value of the ALT_SDMMC_INTMSK_SBE register field. */
#define ALT_SDMMC_INTMSK_SBE_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_SBE field value from a register. */
#define ALT_SDMMC_INTMSK_SBE_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_SDMMC_INTMSK_SBE register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_SBE_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : Auto Command Done - acd
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description              
 * :-----------------------------|:------|:--------------------------
 *  ALT_SDMMC_INTMSK_ACD_E_MSK   | 0x0   | Auto command done Mask   
 *  ALT_SDMMC_INTMSK_ACD_E_NOMSK | 0x1   | Auto command done No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_ACD
 * 
 * Auto command done Mask
 */
#define ALT_SDMMC_INTMSK_ACD_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_ACD
 * 
 * Auto command done No Mask
 */
#define ALT_SDMMC_INTMSK_ACD_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_ACD register field. */
#define ALT_SDMMC_INTMSK_ACD_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_ACD register field. */
#define ALT_SDMMC_INTMSK_ACD_MSB        14
/* The width in bits of the ALT_SDMMC_INTMSK_ACD register field. */
#define ALT_SDMMC_INTMSK_ACD_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_ACD register field value. */
#define ALT_SDMMC_INTMSK_ACD_SET_MSK    0x00004000
/* The mask used to clear the ALT_SDMMC_INTMSK_ACD register field value. */
#define ALT_SDMMC_INTMSK_ACD_CLR_MSK    0xffffbfff
/* The reset value of the ALT_SDMMC_INTMSK_ACD register field. */
#define ALT_SDMMC_INTMSK_ACD_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_ACD field value from a register. */
#define ALT_SDMMC_INTMSK_ACD_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_SDMMC_INTMSK_ACD register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_ACD_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : End-bit Error Read Write no CRC - ebe
 * 
 * Bits used to mask unwanted interrupts. Value of 0 masks interrupts, value of 1
 * enables interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description          
 * :-----------------------------|:------|:----------------------
 *  ALT_SDMMC_INTMSK_EBE_E_MSK   | 0x0   | End-bit error Mask   
 *  ALT_SDMMC_INTMSK_EBE_E_NOMSK | 0x1   | End-bit error No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_EBE
 * 
 * End-bit error Mask
 */
#define ALT_SDMMC_INTMSK_EBE_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_EBE
 * 
 * End-bit error No Mask
 */
#define ALT_SDMMC_INTMSK_EBE_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_EBE register field. */
#define ALT_SDMMC_INTMSK_EBE_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_EBE register field. */
#define ALT_SDMMC_INTMSK_EBE_MSB        15
/* The width in bits of the ALT_SDMMC_INTMSK_EBE register field. */
#define ALT_SDMMC_INTMSK_EBE_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_EBE register field value. */
#define ALT_SDMMC_INTMSK_EBE_SET_MSK    0x00008000
/* The mask used to clear the ALT_SDMMC_INTMSK_EBE register field value. */
#define ALT_SDMMC_INTMSK_EBE_CLR_MSK    0xffff7fff
/* The reset value of the ALT_SDMMC_INTMSK_EBE register field. */
#define ALT_SDMMC_INTMSK_EBE_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_EBE field value from a register. */
#define ALT_SDMMC_INTMSK_EBE_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_SDMMC_INTMSK_EBE register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_EBE_SET(value) (((value) << 15) & 0x00008000)

/*
 * Field : SDIO Interrupt Mask - sdio_int_mask
 * 
 * In current application, MMC-Ver3.3 only Bit 16 of this field is used. Bits 17 to
 * 31 are unused and return 0
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description                 
 * :-------------------------------------|:------|:-----------------------------
 *  ALT_SDMMC_INTMSK_SDIO_INT_MSK_E_DISD | 0x0   | SDIO Mask Interrupt Disabled
 *  ALT_SDMMC_INTMSK_SDIO_INT_MSK_E_END  | 0x1   | SDIO Interrupt Enabled      
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_SDIO_INT_MSK
 * 
 * SDIO Mask Interrupt Disabled
 */
#define ALT_SDMMC_INTMSK_SDIO_INT_MSK_E_DISD    0x0
/*
 * Enumerated value for register field ALT_SDMMC_INTMSK_SDIO_INT_MSK
 * 
 * SDIO Interrupt Enabled
 */
#define ALT_SDMMC_INTMSK_SDIO_INT_MSK_E_END     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_INTMSK_SDIO_INT_MSK register field. */
#define ALT_SDMMC_INTMSK_SDIO_INT_MSK_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_INTMSK_SDIO_INT_MSK register field. */
#define ALT_SDMMC_INTMSK_SDIO_INT_MSK_MSB        16
/* The width in bits of the ALT_SDMMC_INTMSK_SDIO_INT_MSK register field. */
#define ALT_SDMMC_INTMSK_SDIO_INT_MSK_WIDTH      1
/* The mask used to set the ALT_SDMMC_INTMSK_SDIO_INT_MSK register field value. */
#define ALT_SDMMC_INTMSK_SDIO_INT_MSK_SET_MSK    0x00010000
/* The mask used to clear the ALT_SDMMC_INTMSK_SDIO_INT_MSK register field value. */
#define ALT_SDMMC_INTMSK_SDIO_INT_MSK_CLR_MSK    0xfffeffff
/* The reset value of the ALT_SDMMC_INTMSK_SDIO_INT_MSK register field. */
#define ALT_SDMMC_INTMSK_SDIO_INT_MSK_RESET      0x0
/* Extracts the ALT_SDMMC_INTMSK_SDIO_INT_MSK field value from a register. */
#define ALT_SDMMC_INTMSK_SDIO_INT_MSK_GET(value) (((value) & 0x00010000) >> 16)
/* Produces a ALT_SDMMC_INTMSK_SDIO_INT_MSK register field value suitable for setting the register. */
#define ALT_SDMMC_INTMSK_SDIO_INT_MSK_SET(value) (((value) << 16) & 0x00010000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_INTMSK.
 */
struct ALT_SDMMC_INTMSK_s
{
    uint32_t  cd            :  1;  /* Card Detected */
    uint32_t  re            :  1;  /* Response Error */
    uint32_t  cmd           :  1;  /* Command Done */
    uint32_t  dto           :  1;  /* Data Transfer Over */
    uint32_t  txdr          :  1;  /* Transmit FIFO Data Request */
    uint32_t  rxdr          :  1;  /* Receive FIFO Data Request ( */
    uint32_t  rcrc          :  1;  /* Response CRC Error */
    uint32_t  dcrc          :  1;  /* Data CRC Error */
    uint32_t  rto           :  1;  /* Response Timeout */
    uint32_t  drt           :  1;  /* Data Read Timeout */
    uint32_t  hto           :  1;  /* Data Starvation  Host Timeout */
    uint32_t  frun          :  1;  /* FIFO Underrun Overrun Error */
    uint32_t  hle           :  1;  /* Hardware Locked Write Error */
    uint32_t  sbe           :  1;  /* Start-bit Error */
    uint32_t  acd           :  1;  /* Auto Command Done */
    uint32_t  ebe           :  1;  /* End-bit Error Read Write no CRC */
    uint32_t  sdio_int_mask :  1;  /* SDIO Interrupt Mask */
    uint32_t                : 15;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_INTMSK. */
typedef volatile struct ALT_SDMMC_INTMSK_s  ALT_SDMMC_INTMSK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_INTMSK register from the beginning of the component. */
#define ALT_SDMMC_INTMSK_OFST        0x24

/*
 * Register : Command Argument Register - cmdarg
 * 
 * See Field Description.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [31:0] | RW     | 0x0   | Cmd Arg    
 * 
 */
/*
 * Field : Cmd Arg - cmd_arg
 * 
 * Values indicates command argument to be passed to card.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMDARG_CMD_ARG register field. */
#define ALT_SDMMC_CMDARG_CMD_ARG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMDARG_CMD_ARG register field. */
#define ALT_SDMMC_CMDARG_CMD_ARG_MSB        31
/* The width in bits of the ALT_SDMMC_CMDARG_CMD_ARG register field. */
#define ALT_SDMMC_CMDARG_CMD_ARG_WIDTH      32
/* The mask used to set the ALT_SDMMC_CMDARG_CMD_ARG register field value. */
#define ALT_SDMMC_CMDARG_CMD_ARG_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDMMC_CMDARG_CMD_ARG register field value. */
#define ALT_SDMMC_CMDARG_CMD_ARG_CLR_MSK    0x00000000
/* The reset value of the ALT_SDMMC_CMDARG_CMD_ARG register field. */
#define ALT_SDMMC_CMDARG_CMD_ARG_RESET      0x0
/* Extracts the ALT_SDMMC_CMDARG_CMD_ARG field value from a register. */
#define ALT_SDMMC_CMDARG_CMD_ARG_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDMMC_CMDARG_CMD_ARG register field value suitable for setting the register. */
#define ALT_SDMMC_CMDARG_CMD_ARG_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_CMDARG.
 */
struct ALT_SDMMC_CMDARG_s
{
    uint32_t  cmd_arg : 32;  /* Cmd Arg */
};

/* The typedef declaration for register ALT_SDMMC_CMDARG. */
typedef volatile struct ALT_SDMMC_CMDARG_s  ALT_SDMMC_CMDARG_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_CMDARG register from the beginning of the component. */
#define ALT_SDMMC_CMDARG_OFST        0x28

/*
 * Register : Command Register - cmd
 * 
 * This register issues various commands.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                       
 * :--------|:-------|:------|:-----------------------------------
 *  [5:0]   | RW     | 0x0   | Cmd Index                         
 *  [6]     | RW     | 0x0   | Response Expect                   
 *  [7]     | RW     | 0x0   | Response Length                   
 *  [8]     | RW     | 0x0   | Check Response Crc                
 *  [9]     | RW     | 0x0   | Data Transfer Expected            
 *  [10]    | RW     | 0x0   | Read Write                        
 *  [11]    | RW     | 0x0   | Transfer Mode                     
 *  [12]    | RW     | 0x0   | Send Auto Stop                    
 *  [13]    | RW     | 0x0   | Wait Previous Data Complete       
 *  [14]    | RW     | 0x0   | Stop Abort Cmd                    
 *  [15]    | RW     | 0x0   | Send Initialization               
 *  [20:16] | RW     | 0x0   | Card Number                       
 *  [21]    | RW     | 0x0   | Update Clock Registers Only       
 *  [22]    | RW     | 0x0   | Read CE-ATA Device                
 *  [23]    | RW     | 0x0   | Command Completion Signal Expected
 *  [24]    | RW     | 0x0   | Enable Boot                       
 *  [25]    | RW     | 0x0   | Expect Boot Ack                   
 *  [26]    | RW     | 0x0   | Disable Boot                      
 *  [27]    | RW     | 0x0   | Boot Mode                         
 *  [28]    | RW     | 0x0   | Volt Switch                       
 *  [29]    | RW     | 0x1   | Use Hold Reg                      
 *  [30]    | ???    | 0x0   | *UNDEFINED*                       
 *  [31]    | RW     | 0x0   | Start Cmd                         
 * 
 */
/*
 * Field : Cmd Index - cmd_index
 * 
 * Tracks the command index number. Values from 0-31.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_CMD_INDEX register field. */
#define ALT_SDMMC_CMD_CMD_INDEX_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_CMD_INDEX register field. */
#define ALT_SDMMC_CMD_CMD_INDEX_MSB        5
/* The width in bits of the ALT_SDMMC_CMD_CMD_INDEX register field. */
#define ALT_SDMMC_CMD_CMD_INDEX_WIDTH      6
/* The mask used to set the ALT_SDMMC_CMD_CMD_INDEX register field value. */
#define ALT_SDMMC_CMD_CMD_INDEX_SET_MSK    0x0000003f
/* The mask used to clear the ALT_SDMMC_CMD_CMD_INDEX register field value. */
#define ALT_SDMMC_CMD_CMD_INDEX_CLR_MSK    0xffffffc0
/* The reset value of the ALT_SDMMC_CMD_CMD_INDEX register field. */
#define ALT_SDMMC_CMD_CMD_INDEX_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_CMD_INDEX field value from a register. */
#define ALT_SDMMC_CMD_CMD_INDEX_GET(value) (((value) & 0x0000003f) >> 0)
/* Produces a ALT_SDMMC_CMD_CMD_INDEX register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_CMD_INDEX_SET(value) (((value) << 0) & 0x0000003f)

/*
 * Field : Response Expect - response_expect
 * 
 * Response expected from card.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description                   
 * :---------------------------------------|:------|:-------------------------------
 *  ALT_SDMMC_CMD_RESPONSE_EXPECT_E_RESP   | 0x0   | No response expected from card
 *  ALT_SDMMC_CMD_RESPONSE_EXPECT_E_NORESP | 0x1   | Response expected from card   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_RESPONSE_EXPECT
 * 
 * No response expected from card
 */
#define ALT_SDMMC_CMD_RESPONSE_EXPECT_E_RESP    0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_RESPONSE_EXPECT
 * 
 * Response expected from card
 */
#define ALT_SDMMC_CMD_RESPONSE_EXPECT_E_NORESP  0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_RESPONSE_EXPECT register field. */
#define ALT_SDMMC_CMD_RESPONSE_EXPECT_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_RESPONSE_EXPECT register field. */
#define ALT_SDMMC_CMD_RESPONSE_EXPECT_MSB        6
/* The width in bits of the ALT_SDMMC_CMD_RESPONSE_EXPECT register field. */
#define ALT_SDMMC_CMD_RESPONSE_EXPECT_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_RESPONSE_EXPECT register field value. */
#define ALT_SDMMC_CMD_RESPONSE_EXPECT_SET_MSK    0x00000040
/* The mask used to clear the ALT_SDMMC_CMD_RESPONSE_EXPECT register field value. */
#define ALT_SDMMC_CMD_RESPONSE_EXPECT_CLR_MSK    0xffffffbf
/* The reset value of the ALT_SDMMC_CMD_RESPONSE_EXPECT register field. */
#define ALT_SDMMC_CMD_RESPONSE_EXPECT_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_RESPONSE_EXPECT field value from a register. */
#define ALT_SDMMC_CMD_RESPONSE_EXPECT_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_SDMMC_CMD_RESPONSE_EXPECT register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_RESPONSE_EXPECT_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Response Length - response_length
 * 
 * Provides long and short response
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                      
 * :-----------------------------------|:------|:----------------------------------
 *  ALT_SDMMC_CMD_RESPONSE_LEN_E_SHORT | 0x0   | Short response expected from card
 *  ALT_SDMMC_CMD_RESPONSE_LEN_E_LONG  | 0x1   | Long response expected from card 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_RESPONSE_LEN
 * 
 * Short response expected from card
 */
#define ALT_SDMMC_CMD_RESPONSE_LEN_E_SHORT  0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_RESPONSE_LEN
 * 
 * Long response expected from card
 */
#define ALT_SDMMC_CMD_RESPONSE_LEN_E_LONG   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_RESPONSE_LEN register field. */
#define ALT_SDMMC_CMD_RESPONSE_LEN_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_RESPONSE_LEN register field. */
#define ALT_SDMMC_CMD_RESPONSE_LEN_MSB        7
/* The width in bits of the ALT_SDMMC_CMD_RESPONSE_LEN register field. */
#define ALT_SDMMC_CMD_RESPONSE_LEN_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_RESPONSE_LEN register field value. */
#define ALT_SDMMC_CMD_RESPONSE_LEN_SET_MSK    0x00000080
/* The mask used to clear the ALT_SDMMC_CMD_RESPONSE_LEN register field value. */
#define ALT_SDMMC_CMD_RESPONSE_LEN_CLR_MSK    0xffffff7f
/* The reset value of the ALT_SDMMC_CMD_RESPONSE_LEN register field. */
#define ALT_SDMMC_CMD_RESPONSE_LEN_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_RESPONSE_LEN field value from a register. */
#define ALT_SDMMC_CMD_RESPONSE_LEN_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_SDMMC_CMD_RESPONSE_LEN register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_RESPONSE_LEN_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Check Response Crc - check_response_crc
 * 
 * Some of command responses do not return valid CRC bits. Software should disable
 * CRC checks for those commands in order to disable CRC checking by controller.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                     | Value | Description              
 * :-----------------------------------------|:------|:--------------------------
 *  ALT_SDMMC_CMD_CHECK_RESPONSE_CRC_E_NOCHK | 0x0   | Do not check response CRC
 *  ALT_SDMMC_CMD_CHECK_RESPONSE_CRC_E_CHK   | 0x1   | Check Response CRC       
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_CHECK_RESPONSE_CRC
 * 
 * Do not check response CRC
 */
#define ALT_SDMMC_CMD_CHECK_RESPONSE_CRC_E_NOCHK    0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_CHECK_RESPONSE_CRC
 * 
 * Check Response CRC
 */
#define ALT_SDMMC_CMD_CHECK_RESPONSE_CRC_E_CHK      0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_CHECK_RESPONSE_CRC register field. */
#define ALT_SDMMC_CMD_CHECK_RESPONSE_CRC_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_CHECK_RESPONSE_CRC register field. */
#define ALT_SDMMC_CMD_CHECK_RESPONSE_CRC_MSB        8
/* The width in bits of the ALT_SDMMC_CMD_CHECK_RESPONSE_CRC register field. */
#define ALT_SDMMC_CMD_CHECK_RESPONSE_CRC_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_CHECK_RESPONSE_CRC register field value. */
#define ALT_SDMMC_CMD_CHECK_RESPONSE_CRC_SET_MSK    0x00000100
/* The mask used to clear the ALT_SDMMC_CMD_CHECK_RESPONSE_CRC register field value. */
#define ALT_SDMMC_CMD_CHECK_RESPONSE_CRC_CLR_MSK    0xfffffeff
/* The reset value of the ALT_SDMMC_CMD_CHECK_RESPONSE_CRC register field. */
#define ALT_SDMMC_CMD_CHECK_RESPONSE_CRC_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_CHECK_RESPONSE_CRC field value from a register. */
#define ALT_SDMMC_CMD_CHECK_RESPONSE_CRC_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_SDMMC_CMD_CHECK_RESPONSE_CRC register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_CHECK_RESPONSE_CRC_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Data Transfer Expected - data_expected
 * 
 * Set decision on data transfer expecetd or not.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                       | Value | Description                           
 * :-------------------------------------------|:------|:---------------------------------------
 *  ALT_SDMMC_CMD_DATA_EXPECTED_E_NODATXFEREXP | 0x0   | No data transfer expected (read/write)
 *  ALT_SDMMC_CMD_DATA_EXPECTED_E_DATAXFEREXP  | 0x1   | Data transfer expected (read/write)   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_DATA_EXPECTED
 * 
 * No data transfer expected (read/write)
 */
#define ALT_SDMMC_CMD_DATA_EXPECTED_E_NODATXFEREXP  0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_DATA_EXPECTED
 * 
 * Data transfer expected (read/write)
 */
#define ALT_SDMMC_CMD_DATA_EXPECTED_E_DATAXFEREXP   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_DATA_EXPECTED register field. */
#define ALT_SDMMC_CMD_DATA_EXPECTED_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_DATA_EXPECTED register field. */
#define ALT_SDMMC_CMD_DATA_EXPECTED_MSB        9
/* The width in bits of the ALT_SDMMC_CMD_DATA_EXPECTED register field. */
#define ALT_SDMMC_CMD_DATA_EXPECTED_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_DATA_EXPECTED register field value. */
#define ALT_SDMMC_CMD_DATA_EXPECTED_SET_MSK    0x00000200
/* The mask used to clear the ALT_SDMMC_CMD_DATA_EXPECTED register field value. */
#define ALT_SDMMC_CMD_DATA_EXPECTED_CLR_MSK    0xfffffdff
/* The reset value of the ALT_SDMMC_CMD_DATA_EXPECTED register field. */
#define ALT_SDMMC_CMD_DATA_EXPECTED_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_DATA_EXPECTED field value from a register. */
#define ALT_SDMMC_CMD_DATA_EXPECTED_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_SDMMC_CMD_DATA_EXPECTED register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_DATA_EXPECTED_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Read Write - read_write
 * 
 * Read/Write from card. Don't care if no data transfer expected.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                     | Value | Description   
 * :-------------------------|:------|:---------------
 *  ALT_SDMMC_CMD_RD_WR_E_RD | 0x0   | Read from card
 *  ALT_SDMMC_CMD_RD_WR_E_WR | 0x1   | Write to card 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_RD_WR
 * 
 * Read from card
 */
#define ALT_SDMMC_CMD_RD_WR_E_RD    0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_RD_WR
 * 
 * Write to card
 */
#define ALT_SDMMC_CMD_RD_WR_E_WR    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_RD_WR register field. */
#define ALT_SDMMC_CMD_RD_WR_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_RD_WR register field. */
#define ALT_SDMMC_CMD_RD_WR_MSB        10
/* The width in bits of the ALT_SDMMC_CMD_RD_WR register field. */
#define ALT_SDMMC_CMD_RD_WR_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_RD_WR register field value. */
#define ALT_SDMMC_CMD_RD_WR_SET_MSK    0x00000400
/* The mask used to clear the ALT_SDMMC_CMD_RD_WR register field value. */
#define ALT_SDMMC_CMD_RD_WR_CLR_MSK    0xfffffbff
/* The reset value of the ALT_SDMMC_CMD_RD_WR register field. */
#define ALT_SDMMC_CMD_RD_WR_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_RD_WR field value from a register. */
#define ALT_SDMMC_CMD_RD_WR_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_SDMMC_CMD_RD_WR register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_RD_WR_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Transfer Mode - transfer_mode
 * 
 * Block transfer command. Don't care if no data expected
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                 
 * :----------------------------|:------|:-----------------------------
 *  ALT_SDMMC_CMD_TFR_MOD_E_BLK | 0x0   | Block data transfer command 
 *  ALT_SDMMC_CMD_TFR_MOD_E_STR | 0x1   | Stream data transfer command
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_TFR_MOD
 * 
 * Block data transfer command
 */
#define ALT_SDMMC_CMD_TFR_MOD_E_BLK 0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_TFR_MOD
 * 
 * Stream data transfer command
 */
#define ALT_SDMMC_CMD_TFR_MOD_E_STR 0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_TFR_MOD register field. */
#define ALT_SDMMC_CMD_TFR_MOD_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_TFR_MOD register field. */
#define ALT_SDMMC_CMD_TFR_MOD_MSB        11
/* The width in bits of the ALT_SDMMC_CMD_TFR_MOD register field. */
#define ALT_SDMMC_CMD_TFR_MOD_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_TFR_MOD register field value. */
#define ALT_SDMMC_CMD_TFR_MOD_SET_MSK    0x00000800
/* The mask used to clear the ALT_SDMMC_CMD_TFR_MOD register field value. */
#define ALT_SDMMC_CMD_TFR_MOD_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_SDMMC_CMD_TFR_MOD register field. */
#define ALT_SDMMC_CMD_TFR_MOD_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_TFR_MOD field value from a register. */
#define ALT_SDMMC_CMD_TFR_MOD_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_SDMMC_CMD_TFR_MOD register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_TFR_MOD_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : Send Auto Stop - send_auto_stop
 * 
 * When set, SD/MMC sends stop command to SD_MMC_CEATA cards at end of data
 * transfer. Determine the following:
 * 
 * * -when send_auto_stop bit should be set, since some data   transfers do not
 *   need explicit stop commands. *-open-ended transfers that software should
 *   explicitly   send to stop command.
 * 
 * Additionally, when resume is sent to resume- suspended memory access of SD-Combo
 * card, bit should be set correctly if suspended data transfer needs
 * send_auto_stop. Don't care if no data expected from card.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description                                 
 * :--------------------------------------|:------|:---------------------------------------------
 *  ALT_SDMMC_CMD_SEND_AUTO_STOP_E_NOSEND | 0x0   | No stop command sent at end of data transfer
 *  ALT_SDMMC_CMD_SEND_AUTO_STOP_E_SEND   | 0x1   | Send stop command at end of data transfer   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_SEND_AUTO_STOP
 * 
 * No stop command sent at end of data transfer
 */
#define ALT_SDMMC_CMD_SEND_AUTO_STOP_E_NOSEND   0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_SEND_AUTO_STOP
 * 
 * Send stop command at end of data transfer
 */
#define ALT_SDMMC_CMD_SEND_AUTO_STOP_E_SEND     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_SEND_AUTO_STOP register field. */
#define ALT_SDMMC_CMD_SEND_AUTO_STOP_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_SEND_AUTO_STOP register field. */
#define ALT_SDMMC_CMD_SEND_AUTO_STOP_MSB        12
/* The width in bits of the ALT_SDMMC_CMD_SEND_AUTO_STOP register field. */
#define ALT_SDMMC_CMD_SEND_AUTO_STOP_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_SEND_AUTO_STOP register field value. */
#define ALT_SDMMC_CMD_SEND_AUTO_STOP_SET_MSK    0x00001000
/* The mask used to clear the ALT_SDMMC_CMD_SEND_AUTO_STOP register field value. */
#define ALT_SDMMC_CMD_SEND_AUTO_STOP_CLR_MSK    0xffffefff
/* The reset value of the ALT_SDMMC_CMD_SEND_AUTO_STOP register field. */
#define ALT_SDMMC_CMD_SEND_AUTO_STOP_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_SEND_AUTO_STOP field value from a register. */
#define ALT_SDMMC_CMD_SEND_AUTO_STOP_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_SDMMC_CMD_SEND_AUTO_STOP register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_SEND_AUTO_STOP_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : Wait Previous Data Complete - wait_prvdata_complete
 * 
 * Determines when command is sent. The send command at once option is typically
 * used to query status of card during data transfer or to stop current data
 * transfer.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                         | Value | Description                               
 * :---------------------------------------------|:------|:-------------------------------------------
 *  ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE_E_NOWAIT | 0x0   | Send command at once                      
 *  ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE_E_WAIT   | 0x1   | Wait for previous data transfer completion
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE
 * 
 * Send command at once
 */
#define ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE_E_NOWAIT    0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE
 * 
 * Wait for previous data transfer completion
 */
#define ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE_E_WAIT      0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE register field. */
#define ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE register field. */
#define ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE_MSB        13
/* The width in bits of the ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE register field. */
#define ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE register field value. */
#define ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE_SET_MSK    0x00002000
/* The mask used to clear the ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE register field value. */
#define ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE_CLR_MSK    0xffffdfff
/* The reset value of the ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE register field. */
#define ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE field value from a register. */
#define ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_WAIT_PRVDATA_COMPLETE_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : Stop Abort Cmd - stop_abort_cmd
 * 
 * When open-ended or predefined data transfer is in progress, and host issues stop
 * or abort command to stop data transfer, bit should be set so that command/data
 * state-machines of CIU can return correctly to idle state. This is also
 * applicable for Boot mode transfers. To Abort boot mode, this bit should be set
 * along with CMD[26] = disable_boot.
 * 
 * Note: If abort is sent to function-number currently selected or not in data-
 * transfer mode, then bit should be set to 0.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                    | Value | Description                                     
 * :----------------------------------------|:------|:-------------------------------------------------
 *  ALT_SDMMC_CMD_STOP_ABT_CMD_E_NOSTOPABRT | 0x0   | Don't stop or abort command to stop current data
 * :                                        |       | transfer in progress                            
 *  ALT_SDMMC_CMD_STOP_ABT_CMD_E_STOPABRT   | 0x1   | Stop or Abort command, intended to stop current 
 * :                                        |       | data transfer in progress                       
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_STOP_ABT_CMD
 * 
 * Don't stop or abort command to stop current data transfer in progress
 */
#define ALT_SDMMC_CMD_STOP_ABT_CMD_E_NOSTOPABRT 0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_STOP_ABT_CMD
 * 
 * Stop or Abort command, intended to stop current data transfer in progress
 */
#define ALT_SDMMC_CMD_STOP_ABT_CMD_E_STOPABRT   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_STOP_ABT_CMD register field. */
#define ALT_SDMMC_CMD_STOP_ABT_CMD_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_STOP_ABT_CMD register field. */
#define ALT_SDMMC_CMD_STOP_ABT_CMD_MSB        14
/* The width in bits of the ALT_SDMMC_CMD_STOP_ABT_CMD register field. */
#define ALT_SDMMC_CMD_STOP_ABT_CMD_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_STOP_ABT_CMD register field value. */
#define ALT_SDMMC_CMD_STOP_ABT_CMD_SET_MSK    0x00004000
/* The mask used to clear the ALT_SDMMC_CMD_STOP_ABT_CMD register field value. */
#define ALT_SDMMC_CMD_STOP_ABT_CMD_CLR_MSK    0xffffbfff
/* The reset value of the ALT_SDMMC_CMD_STOP_ABT_CMD register field. */
#define ALT_SDMMC_CMD_STOP_ABT_CMD_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_STOP_ABT_CMD field value from a register. */
#define ALT_SDMMC_CMD_STOP_ABT_CMD_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_SDMMC_CMD_STOP_ABT_CMD register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_STOP_ABT_CMD_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : Send Initialization - send_initialization
 * 
 * After power on, 80 clocks must be sent to the card for initialization before
 * sending any commands to card. Bit should be set while sending first command to
 * card so that controller will initialize clocks before sending command to card.
 * This bit should not be set for either of the boot modes (alternate or
 * mandatory).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                       | Value | Description                                     
 * :-------------------------------------------|:------|:-------------------------------------------------
 *  ALT_SDMMC_CMD_SEND_INITIALIZATION_E_NOINIT | 0x0   | Do not send initialization sequence (80 clocks  
 * :                                           |       | of 1) before sending this command               
 *  ALT_SDMMC_CMD_SEND_INITIALIZATION_E_INIT   | 0x1   | Send initialization sequence before sending this
 * :                                           |       | command                                         
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_SEND_INITIALIZATION
 * 
 * Do not send initialization sequence (80 clocks of 1) before sending this command
 */
#define ALT_SDMMC_CMD_SEND_INITIALIZATION_E_NOINIT  0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_SEND_INITIALIZATION
 * 
 * Send initialization sequence before sending this command
 */
#define ALT_SDMMC_CMD_SEND_INITIALIZATION_E_INIT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_SEND_INITIALIZATION register field. */
#define ALT_SDMMC_CMD_SEND_INITIALIZATION_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_SEND_INITIALIZATION register field. */
#define ALT_SDMMC_CMD_SEND_INITIALIZATION_MSB        15
/* The width in bits of the ALT_SDMMC_CMD_SEND_INITIALIZATION register field. */
#define ALT_SDMMC_CMD_SEND_INITIALIZATION_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_SEND_INITIALIZATION register field value. */
#define ALT_SDMMC_CMD_SEND_INITIALIZATION_SET_MSK    0x00008000
/* The mask used to clear the ALT_SDMMC_CMD_SEND_INITIALIZATION register field value. */
#define ALT_SDMMC_CMD_SEND_INITIALIZATION_CLR_MSK    0xffff7fff
/* The reset value of the ALT_SDMMC_CMD_SEND_INITIALIZATION register field. */
#define ALT_SDMMC_CMD_SEND_INITIALIZATION_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_SEND_INITIALIZATION field value from a register. */
#define ALT_SDMMC_CMD_SEND_INITIALIZATION_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_SDMMC_CMD_SEND_INITIALIZATION register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_SEND_INITIALIZATION_SET(value) (((value) << 15) & 0x00008000)

/*
 * Field : Card Number - card_number
 * 
 * Card number in use must always be 0.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_CARD_NUMBER register field. */
#define ALT_SDMMC_CMD_CARD_NUMBER_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_CARD_NUMBER register field. */
#define ALT_SDMMC_CMD_CARD_NUMBER_MSB        20
/* The width in bits of the ALT_SDMMC_CMD_CARD_NUMBER register field. */
#define ALT_SDMMC_CMD_CARD_NUMBER_WIDTH      5
/* The mask used to set the ALT_SDMMC_CMD_CARD_NUMBER register field value. */
#define ALT_SDMMC_CMD_CARD_NUMBER_SET_MSK    0x001f0000
/* The mask used to clear the ALT_SDMMC_CMD_CARD_NUMBER register field value. */
#define ALT_SDMMC_CMD_CARD_NUMBER_CLR_MSK    0xffe0ffff
/* The reset value of the ALT_SDMMC_CMD_CARD_NUMBER register field. */
#define ALT_SDMMC_CMD_CARD_NUMBER_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_CARD_NUMBER field value from a register. */
#define ALT_SDMMC_CMD_CARD_NUMBER_GET(value) (((value) & 0x001f0000) >> 16)
/* Produces a ALT_SDMMC_CMD_CARD_NUMBER register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_CARD_NUMBER_SET(value) (((value) << 16) & 0x001f0000)

/*
 * Field : Update Clock Registers Only - update_clock_registers_only
 * 
 * Following register values transferred into card clock domain: CLKDIV, CLRSRC,
 * CLKENA.
 * 
 * Changes card clocks (change frequency, truncate off or on, and set low-frequency
 * mode); provided in order to change clock frequency or stop clock without having
 * to send command to cards. During normal command sequence, when
 * update_clock_registers_only = 0, following control registers are transferred
 * from BIU to CIU: CMD, CMDARG, TMOUT, CTYPE, BLKSIZ, BYTCNT. CIU uses new
 * register values for new command sequence to card(s). When bit is set, there are
 * no Command Done interrupts because no command is sent to SD_MMC_CEATA cards.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                             | Value | Description                                     
 * :-------------------------------------------------|:------|:-------------------------------------------------
 *  ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY_E_NORMCMD     | 0x0   | Normal command sequence                         
 *  ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY_E_UPDATCLKREG | 0x1   | Do not send commands, just update clock register
 * :                                                 |       | value into card clock domain                    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY
 * 
 * Normal command sequence
 */
#define ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY_E_NORMCMD        0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY
 * 
 * Do not send commands, just update clock register value into card clock domain
 */
#define ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY_E_UPDATCLKREG    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY register field. */
#define ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY_LSB        21
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY register field. */
#define ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY_MSB        21
/* The width in bits of the ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY register field. */
#define ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY register field value. */
#define ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY_SET_MSK    0x00200000
/* The mask used to clear the ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY register field value. */
#define ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY_CLR_MSK    0xffdfffff
/* The reset value of the ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY register field. */
#define ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY field value from a register. */
#define ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY_GET(value) (((value) & 0x00200000) >> 21)
/* Produces a ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_UPDATE_CLK_REGS_ONLY_SET(value) (((value) << 21) & 0x00200000)

/*
 * Field : Read CE-ATA Device - read_ceata_device
 * 
 * Software should set this bit to indicate that CE-ATA device is being accessed
 * for read transfer. This bit is used to disable read data timeout indication
 * while performing CE-ATA read transfers. Maximum value of I/O transmission delay
 * can be no less than 10 seconds. SD/MMC should not indicate read data timeout
 * while waiting for data from CE-ATA device.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description                                  
 * :-------------------------------------|:------|:----------------------------------------------
 *  ALT_SDMMC_CMD_RD_CEATA_DEVICE_E_NORD | 0x0   | Host is not performing read access (RW_REG or
 * :                                     |       | RW_BLK) towards CE-ATA device                
 *  ALT_SDMMC_CMD_RD_CEATA_DEVICE_E_RD   | 0x1   | Host is performing read access (RW_REG or    
 * :                                     |       | RW_BLK) towards CE-ATA device                
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_RD_CEATA_DEVICE
 * 
 * Host is not performing read access (RW_REG or RW_BLK) towards CE-ATA device
 */
#define ALT_SDMMC_CMD_RD_CEATA_DEVICE_E_NORD    0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_RD_CEATA_DEVICE
 * 
 * Host is performing read access (RW_REG or RW_BLK) towards CE-ATA device
 */
#define ALT_SDMMC_CMD_RD_CEATA_DEVICE_E_RD      0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_RD_CEATA_DEVICE register field. */
#define ALT_SDMMC_CMD_RD_CEATA_DEVICE_LSB        22
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_RD_CEATA_DEVICE register field. */
#define ALT_SDMMC_CMD_RD_CEATA_DEVICE_MSB        22
/* The width in bits of the ALT_SDMMC_CMD_RD_CEATA_DEVICE register field. */
#define ALT_SDMMC_CMD_RD_CEATA_DEVICE_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_RD_CEATA_DEVICE register field value. */
#define ALT_SDMMC_CMD_RD_CEATA_DEVICE_SET_MSK    0x00400000
/* The mask used to clear the ALT_SDMMC_CMD_RD_CEATA_DEVICE register field value. */
#define ALT_SDMMC_CMD_RD_CEATA_DEVICE_CLR_MSK    0xffbfffff
/* The reset value of the ALT_SDMMC_CMD_RD_CEATA_DEVICE register field. */
#define ALT_SDMMC_CMD_RD_CEATA_DEVICE_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_RD_CEATA_DEVICE field value from a register. */
#define ALT_SDMMC_CMD_RD_CEATA_DEVICE_GET(value) (((value) & 0x00400000) >> 22)
/* Produces a ALT_SDMMC_CMD_RD_CEATA_DEVICE register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_RD_CEATA_DEVICE_SET(value) (((value) << 22) & 0x00400000)

/*
 * Field : Command Completion Signal Expected - ccs_expected
 * 
 * If the command expects Command Completion Signal (CCS) from the CE-ATA device,
 * the software should set this control bit. SD/MMC sets Data Transfer Over (DTO)
 * bit in RINTSTS register and generates interrupt to host if Data Transfer Over
 * interrupt is not masked.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                    
 * :----------------------------------|:------|:------------------------------------------------
 *  ALT_SDMMC_CMD_CCS_EXPECTED_E_DISD | 0x0   | Interrupts are not enabled in CE-ATA device    
 * :                                  |       | (nIEN = 1 in ATA control register), or command 
 * :                                  |       | does not expect CCS from device                
 *  ALT_SDMMC_CMD_CCS_EXPECTED_E_END  | 0x1   | Interrupts are enabled in CE-ATA device (nIEN =
 * :                                  |       | 0), and RW_BLK command expects command         
 * :                                  |       | completion signal from CE-ATA device           
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_CCS_EXPECTED
 * 
 * Interrupts are not enabled in CE-ATA device (nIEN = 1 in ATA control register),
 * or command does not expect CCS from device
 */
#define ALT_SDMMC_CMD_CCS_EXPECTED_E_DISD   0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_CCS_EXPECTED
 * 
 * Interrupts are enabled in CE-ATA device (nIEN = 0), and RW_BLK command expects
 * command completion signal from CE-ATA device
 */
#define ALT_SDMMC_CMD_CCS_EXPECTED_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_CCS_EXPECTED register field. */
#define ALT_SDMMC_CMD_CCS_EXPECTED_LSB        23
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_CCS_EXPECTED register field. */
#define ALT_SDMMC_CMD_CCS_EXPECTED_MSB        23
/* The width in bits of the ALT_SDMMC_CMD_CCS_EXPECTED register field. */
#define ALT_SDMMC_CMD_CCS_EXPECTED_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_CCS_EXPECTED register field value. */
#define ALT_SDMMC_CMD_CCS_EXPECTED_SET_MSK    0x00800000
/* The mask used to clear the ALT_SDMMC_CMD_CCS_EXPECTED register field value. */
#define ALT_SDMMC_CMD_CCS_EXPECTED_CLR_MSK    0xff7fffff
/* The reset value of the ALT_SDMMC_CMD_CCS_EXPECTED register field. */
#define ALT_SDMMC_CMD_CCS_EXPECTED_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_CCS_EXPECTED field value from a register. */
#define ALT_SDMMC_CMD_CCS_EXPECTED_GET(value) (((value) & 0x00800000) >> 23)
/* Produces a ALT_SDMMC_CMD_CCS_EXPECTED register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_CCS_EXPECTED_SET(value) (((value) << 23) & 0x00800000)

/*
 * Field : Enable Boot - enable_boot
 * 
 * This bit should be set only for mandatory boot mode. When Software sets this bit
 * along with start_cmd, CIU starts the boot sequence for the corresponding card by
 * asserting the CMD line low. Do NOT set disable_boot and enable_boot together
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description 
 * :-----------------------------|:------|:-------------
 *  ALT_SDMMC_CMD_EN_BOOT_E_DISD | 0x0   | Disable Boot
 *  ALT_SDMMC_CMD_EN_BOOT_E_END  | 0x1   | Enable Boot 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_EN_BOOT
 * 
 * Disable Boot
 */
#define ALT_SDMMC_CMD_EN_BOOT_E_DISD    0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_EN_BOOT
 * 
 * Enable Boot
 */
#define ALT_SDMMC_CMD_EN_BOOT_E_END     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_EN_BOOT register field. */
#define ALT_SDMMC_CMD_EN_BOOT_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_EN_BOOT register field. */
#define ALT_SDMMC_CMD_EN_BOOT_MSB        24
/* The width in bits of the ALT_SDMMC_CMD_EN_BOOT register field. */
#define ALT_SDMMC_CMD_EN_BOOT_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_EN_BOOT register field value. */
#define ALT_SDMMC_CMD_EN_BOOT_SET_MSK    0x01000000
/* The mask used to clear the ALT_SDMMC_CMD_EN_BOOT register field value. */
#define ALT_SDMMC_CMD_EN_BOOT_CLR_MSK    0xfeffffff
/* The reset value of the ALT_SDMMC_CMD_EN_BOOT register field. */
#define ALT_SDMMC_CMD_EN_BOOT_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_EN_BOOT field value from a register. */
#define ALT_SDMMC_CMD_EN_BOOT_GET(value) (((value) & 0x01000000) >> 24)
/* Produces a ALT_SDMMC_CMD_EN_BOOT register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_EN_BOOT_SET(value) (((value) << 24) & 0x01000000)

/*
 * Field : Expect Boot Ack - expect_boot_ack
 * 
 * When Software sets this bit along with enable_boot, CIU expects a boot
 * acknowledge start pattern of 0-1-0 from the selected card.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description    
 * :------------------------------------------|:------|:----------------
 *  ALT_SDMMC_CMD_EXPECT_BOOT_ACK_E_NOBOOTACK | 0x0   | No Boot ACK    
 *  ALT_SDMMC_CMD_EXPECT_BOOT_ACK_E_BOOTACK   | 0x1   | Expect Boot ACK
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_EXPECT_BOOT_ACK
 * 
 * No Boot ACK
 */
#define ALT_SDMMC_CMD_EXPECT_BOOT_ACK_E_NOBOOTACK   0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_EXPECT_BOOT_ACK
 * 
 * Expect Boot ACK
 */
#define ALT_SDMMC_CMD_EXPECT_BOOT_ACK_E_BOOTACK     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_EXPECT_BOOT_ACK register field. */
#define ALT_SDMMC_CMD_EXPECT_BOOT_ACK_LSB        25
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_EXPECT_BOOT_ACK register field. */
#define ALT_SDMMC_CMD_EXPECT_BOOT_ACK_MSB        25
/* The width in bits of the ALT_SDMMC_CMD_EXPECT_BOOT_ACK register field. */
#define ALT_SDMMC_CMD_EXPECT_BOOT_ACK_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_EXPECT_BOOT_ACK register field value. */
#define ALT_SDMMC_CMD_EXPECT_BOOT_ACK_SET_MSK    0x02000000
/* The mask used to clear the ALT_SDMMC_CMD_EXPECT_BOOT_ACK register field value. */
#define ALT_SDMMC_CMD_EXPECT_BOOT_ACK_CLR_MSK    0xfdffffff
/* The reset value of the ALT_SDMMC_CMD_EXPECT_BOOT_ACK register field. */
#define ALT_SDMMC_CMD_EXPECT_BOOT_ACK_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_EXPECT_BOOT_ACK field value from a register. */
#define ALT_SDMMC_CMD_EXPECT_BOOT_ACK_GET(value) (((value) & 0x02000000) >> 25)
/* Produces a ALT_SDMMC_CMD_EXPECT_BOOT_ACK register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_EXPECT_BOOT_ACK_SET(value) (((value) << 25) & 0x02000000)

/*
 * Field : Disable Boot - disable_boot
 * 
 * When software sets this bit along with start_cmd, CIU terminates the boot
 * operation. Do NOT set disable_boot and enable_boot together.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description        
 * :------------------------------------|:------|:--------------------
 *  ALT_SDMMC_CMD_DIS_BOOT_E_NOTERMBOOT | 0x0   | Boot not Terminated
 *  ALT_SDMMC_CMD_DIS_BOOT_E_TERMBOOT   | 0x1   | Terminate Boot     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_DIS_BOOT
 * 
 * Boot not Terminated
 */
#define ALT_SDMMC_CMD_DIS_BOOT_E_NOTERMBOOT 0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_DIS_BOOT
 * 
 * Terminate Boot
 */
#define ALT_SDMMC_CMD_DIS_BOOT_E_TERMBOOT   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_DIS_BOOT register field. */
#define ALT_SDMMC_CMD_DIS_BOOT_LSB        26
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_DIS_BOOT register field. */
#define ALT_SDMMC_CMD_DIS_BOOT_MSB        26
/* The width in bits of the ALT_SDMMC_CMD_DIS_BOOT register field. */
#define ALT_SDMMC_CMD_DIS_BOOT_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_DIS_BOOT register field value. */
#define ALT_SDMMC_CMD_DIS_BOOT_SET_MSK    0x04000000
/* The mask used to clear the ALT_SDMMC_CMD_DIS_BOOT register field value. */
#define ALT_SDMMC_CMD_DIS_BOOT_CLR_MSK    0xfbffffff
/* The reset value of the ALT_SDMMC_CMD_DIS_BOOT register field. */
#define ALT_SDMMC_CMD_DIS_BOOT_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_DIS_BOOT field value from a register. */
#define ALT_SDMMC_CMD_DIS_BOOT_GET(value) (((value) & 0x04000000) >> 26)
/* Produces a ALT_SDMMC_CMD_DIS_BOOT register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_DIS_BOOT_SET(value) (((value) << 26) & 0x04000000)

/*
 * Field : Boot Mode - boot_mode
 * 
 * Type of Boot Mode.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description             
 * :-----------------------------------|:------|:-------------------------
 *  ALT_SDMMC_CMD_BOOT_MOD_E_MANDATORY | 0x0   | Mandatory Boot Operation
 *  ALT_SDMMC_CMD_BOOT_MOD_E_ALTERNATE | 0x1   | Alternate Boot Operation
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_BOOT_MOD
 * 
 * Mandatory Boot Operation
 */
#define ALT_SDMMC_CMD_BOOT_MOD_E_MANDATORY  0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_BOOT_MOD
 * 
 * Alternate Boot Operation
 */
#define ALT_SDMMC_CMD_BOOT_MOD_E_ALTERNATE  0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_BOOT_MOD register field. */
#define ALT_SDMMC_CMD_BOOT_MOD_LSB        27
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_BOOT_MOD register field. */
#define ALT_SDMMC_CMD_BOOT_MOD_MSB        27
/* The width in bits of the ALT_SDMMC_CMD_BOOT_MOD register field. */
#define ALT_SDMMC_CMD_BOOT_MOD_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_BOOT_MOD register field value. */
#define ALT_SDMMC_CMD_BOOT_MOD_SET_MSK    0x08000000
/* The mask used to clear the ALT_SDMMC_CMD_BOOT_MOD register field value. */
#define ALT_SDMMC_CMD_BOOT_MOD_CLR_MSK    0xf7ffffff
/* The reset value of the ALT_SDMMC_CMD_BOOT_MOD register field. */
#define ALT_SDMMC_CMD_BOOT_MOD_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_BOOT_MOD field value from a register. */
#define ALT_SDMMC_CMD_BOOT_MOD_GET(value) (((value) & 0x08000000) >> 27)
/* Produces a ALT_SDMMC_CMD_BOOT_MOD register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_BOOT_MOD_SET(value) (((value) << 27) & 0x08000000)

/*
 * Field : Volt Switch - volt_switch
 * 
 * Voltage switch bit. When set must be set for CMD11 only.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description                   
 * :-------------------------------------|:------|:-------------------------------
 *  ALT_SDMMC_CMD_VOLT_SWITCH_E_NOVOLTSW | 0x0   | No voltage switching - default
 *  ALT_SDMMC_CMD_VOLT_SWITCH_E_VOLTSW   | 0x1   | Voltage switching enabled     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_VOLT_SWITCH
 * 
 * No voltage switching - default
 */
#define ALT_SDMMC_CMD_VOLT_SWITCH_E_NOVOLTSW    0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_VOLT_SWITCH
 * 
 * Voltage switching enabled
 */
#define ALT_SDMMC_CMD_VOLT_SWITCH_E_VOLTSW      0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_VOLT_SWITCH register field. */
#define ALT_SDMMC_CMD_VOLT_SWITCH_LSB        28
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_VOLT_SWITCH register field. */
#define ALT_SDMMC_CMD_VOLT_SWITCH_MSB        28
/* The width in bits of the ALT_SDMMC_CMD_VOLT_SWITCH register field. */
#define ALT_SDMMC_CMD_VOLT_SWITCH_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_VOLT_SWITCH register field value. */
#define ALT_SDMMC_CMD_VOLT_SWITCH_SET_MSK    0x10000000
/* The mask used to clear the ALT_SDMMC_CMD_VOLT_SWITCH register field value. */
#define ALT_SDMMC_CMD_VOLT_SWITCH_CLR_MSK    0xefffffff
/* The reset value of the ALT_SDMMC_CMD_VOLT_SWITCH register field. */
#define ALT_SDMMC_CMD_VOLT_SWITCH_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_VOLT_SWITCH field value from a register. */
#define ALT_SDMMC_CMD_VOLT_SWITCH_GET(value) (((value) & 0x10000000) >> 28)
/* Produces a ALT_SDMMC_CMD_VOLT_SWITCH register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_VOLT_SWITCH_SET(value) (((value) << 28) & 0x10000000)

/*
 * Field : Use Hold Reg - use_hold_reg
 * 
 * Set to one for SDR12 and SDR25 (with non-zero phase-shifted cclk_in_drv); zero
 * phase shift is not allowed in these modes.
 * 
 * * Set to 1'b0 for SDR50, SDR104, and DDR50 (with zero  phase-shifted
 *   cclk_in_drv).
 * 
 * * Set to 1'b1 for SDR50, SDR104, and DDR50  (with non-zero phase-shifted
 *   cclk_in_drv).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description                               
 * :--------------------------------------|:------|:-------------------------------------------
 *  ALT_SDMMC_CMD_USE_HOLD_REG_E_BYPASS   | 0x0   | CMD and DATA sent to card bypassing HOLD  
 * :                                      |       | Register                                  
 *  ALT_SDMMC_CMD_USE_HOLD_REG_E_NOBYPASS | 0x1   | CMD and DATA sent to card through the HOLD
 * :                                      |       | Register                                  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_USE_HOLD_REG
 * 
 * CMD and DATA sent to card bypassing HOLD Register
 */
#define ALT_SDMMC_CMD_USE_HOLD_REG_E_BYPASS     0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_USE_HOLD_REG
 * 
 * CMD and DATA sent to card through the HOLD Register
 */
#define ALT_SDMMC_CMD_USE_HOLD_REG_E_NOBYPASS   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_USE_HOLD_REG register field. */
#define ALT_SDMMC_CMD_USE_HOLD_REG_LSB        29
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_USE_HOLD_REG register field. */
#define ALT_SDMMC_CMD_USE_HOLD_REG_MSB        29
/* The width in bits of the ALT_SDMMC_CMD_USE_HOLD_REG register field. */
#define ALT_SDMMC_CMD_USE_HOLD_REG_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_USE_HOLD_REG register field value. */
#define ALT_SDMMC_CMD_USE_HOLD_REG_SET_MSK    0x20000000
/* The mask used to clear the ALT_SDMMC_CMD_USE_HOLD_REG register field value. */
#define ALT_SDMMC_CMD_USE_HOLD_REG_CLR_MSK    0xdfffffff
/* The reset value of the ALT_SDMMC_CMD_USE_HOLD_REG register field. */
#define ALT_SDMMC_CMD_USE_HOLD_REG_RESET      0x1
/* Extracts the ALT_SDMMC_CMD_USE_HOLD_REG field value from a register. */
#define ALT_SDMMC_CMD_USE_HOLD_REG_GET(value) (((value) & 0x20000000) >> 29)
/* Produces a ALT_SDMMC_CMD_USE_HOLD_REG register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_USE_HOLD_REG_SET(value) (((value) << 29) & 0x20000000)

/*
 * Field : Start Cmd - start_cmd
 * 
 * Once command is taken by CIU, bit is cleared. If Start Cmd issued host should
 * not attempt to write to any command registers. If write is attempted, hardware
 * lock error is set in raw interrupt register. Once command is sent and response
 * is received from SD_MMC_CEATA cards, Command Done bit is set in raw interrupt
 * register.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description     
 * :----------------------------------|:------|:-----------------
 *  ALT_SDMMC_CMD_START_CMD_E_NOSTART | 0x0   | No Start Cmd    
 *  ALT_SDMMC_CMD_START_CMD_E_START   | 0x1   | Start Cmd Issued
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CMD_START_CMD
 * 
 * No Start Cmd
 */
#define ALT_SDMMC_CMD_START_CMD_E_NOSTART   0x0
/*
 * Enumerated value for register field ALT_SDMMC_CMD_START_CMD
 * 
 * Start Cmd Issued
 */
#define ALT_SDMMC_CMD_START_CMD_E_START     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CMD_START_CMD register field. */
#define ALT_SDMMC_CMD_START_CMD_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CMD_START_CMD register field. */
#define ALT_SDMMC_CMD_START_CMD_MSB        31
/* The width in bits of the ALT_SDMMC_CMD_START_CMD register field. */
#define ALT_SDMMC_CMD_START_CMD_WIDTH      1
/* The mask used to set the ALT_SDMMC_CMD_START_CMD register field value. */
#define ALT_SDMMC_CMD_START_CMD_SET_MSK    0x80000000
/* The mask used to clear the ALT_SDMMC_CMD_START_CMD register field value. */
#define ALT_SDMMC_CMD_START_CMD_CLR_MSK    0x7fffffff
/* The reset value of the ALT_SDMMC_CMD_START_CMD register field. */
#define ALT_SDMMC_CMD_START_CMD_RESET      0x0
/* Extracts the ALT_SDMMC_CMD_START_CMD field value from a register. */
#define ALT_SDMMC_CMD_START_CMD_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_SDMMC_CMD_START_CMD register field value suitable for setting the register. */
#define ALT_SDMMC_CMD_START_CMD_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_CMD.
 */
struct ALT_SDMMC_CMD_s
{
    uint32_t  cmd_index                   :  6;  /* Cmd Index */
    uint32_t  response_expect             :  1;  /* Response Expect */
    uint32_t  response_length             :  1;  /* Response Length */
    uint32_t  check_response_crc          :  1;  /* Check Response Crc */
    uint32_t  data_expected               :  1;  /* Data Transfer Expected */
    uint32_t  read_write                  :  1;  /* Read Write */
    uint32_t  transfer_mode               :  1;  /* Transfer Mode */
    uint32_t  send_auto_stop              :  1;  /* Send Auto Stop */
    uint32_t  wait_prvdata_complete       :  1;  /* Wait Previous Data Complete */
    uint32_t  stop_abort_cmd              :  1;  /* Stop Abort Cmd */
    uint32_t  send_initialization         :  1;  /* Send Initialization */
    uint32_t  card_number                 :  5;  /* Card Number */
    uint32_t  update_clock_registers_only :  1;  /* Update Clock Registers Only */
    uint32_t  read_ceata_device           :  1;  /* Read CE-ATA Device */
    uint32_t  ccs_expected                :  1;  /* Command Completion Signal Expected */
    uint32_t  enable_boot                 :  1;  /* Enable Boot */
    uint32_t  expect_boot_ack             :  1;  /* Expect Boot Ack */
    uint32_t  disable_boot                :  1;  /* Disable Boot */
    uint32_t  boot_mode                   :  1;  /* Boot Mode */
    uint32_t  volt_switch                 :  1;  /* Volt Switch */
    uint32_t  use_hold_reg                :  1;  /* Use Hold Reg */
    uint32_t                              :  1;  /* *UNDEFINED* */
    uint32_t  start_cmd                   :  1;  /* Start Cmd */
};

/* The typedef declaration for register ALT_SDMMC_CMD. */
typedef volatile struct ALT_SDMMC_CMD_s  ALT_SDMMC_CMD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_CMD register from the beginning of the component. */
#define ALT_SDMMC_CMD_OFST        0x2c

/*
 * Register : Response Register 0 - resp0
 * 
 * Preserves previous command.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [31:0] | R      | 0x0   | Response 0 
 * 
 */
/*
 * Field : Response 0 - response0
 * 
 * Bit[31:0] of response.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RESP0_RESPONSE0 register field. */
#define ALT_SDMMC_RESP0_RESPONSE0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RESP0_RESPONSE0 register field. */
#define ALT_SDMMC_RESP0_RESPONSE0_MSB        31
/* The width in bits of the ALT_SDMMC_RESP0_RESPONSE0 register field. */
#define ALT_SDMMC_RESP0_RESPONSE0_WIDTH      32
/* The mask used to set the ALT_SDMMC_RESP0_RESPONSE0 register field value. */
#define ALT_SDMMC_RESP0_RESPONSE0_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDMMC_RESP0_RESPONSE0 register field value. */
#define ALT_SDMMC_RESP0_RESPONSE0_CLR_MSK    0x00000000
/* The reset value of the ALT_SDMMC_RESP0_RESPONSE0 register field. */
#define ALT_SDMMC_RESP0_RESPONSE0_RESET      0x0
/* Extracts the ALT_SDMMC_RESP0_RESPONSE0 field value from a register. */
#define ALT_SDMMC_RESP0_RESPONSE0_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDMMC_RESP0_RESPONSE0 register field value suitable for setting the register. */
#define ALT_SDMMC_RESP0_RESPONSE0_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_RESP0.
 */
struct ALT_SDMMC_RESP0_s
{
    const uint32_t  response0 : 32;  /* Response 0 */
};

/* The typedef declaration for register ALT_SDMMC_RESP0. */
typedef volatile struct ALT_SDMMC_RESP0_s  ALT_SDMMC_RESP0_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_RESP0 register from the beginning of the component. */
#define ALT_SDMMC_RESP0_OFST        0x30

/*
 * Register : Response Register 1 - resp1
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [31:0] | R      | 0x0   | Response 1 
 * 
 */
/*
 * Field : Response 1 - response1
 * 
 * Register represents bit[63:32] of long response. When CIU sends auto-stop
 * command, then response is saved in register. Response for previous command sent
 * by host is still preserved in Response 0 register. Additional auto-stop issued
 * only for data transfer commands, and response type is always short for them.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RESP1_RESPONSE1 register field. */
#define ALT_SDMMC_RESP1_RESPONSE1_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RESP1_RESPONSE1 register field. */
#define ALT_SDMMC_RESP1_RESPONSE1_MSB        31
/* The width in bits of the ALT_SDMMC_RESP1_RESPONSE1 register field. */
#define ALT_SDMMC_RESP1_RESPONSE1_WIDTH      32
/* The mask used to set the ALT_SDMMC_RESP1_RESPONSE1 register field value. */
#define ALT_SDMMC_RESP1_RESPONSE1_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDMMC_RESP1_RESPONSE1 register field value. */
#define ALT_SDMMC_RESP1_RESPONSE1_CLR_MSK    0x00000000
/* The reset value of the ALT_SDMMC_RESP1_RESPONSE1 register field. */
#define ALT_SDMMC_RESP1_RESPONSE1_RESET      0x0
/* Extracts the ALT_SDMMC_RESP1_RESPONSE1 field value from a register. */
#define ALT_SDMMC_RESP1_RESPONSE1_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDMMC_RESP1_RESPONSE1 register field value suitable for setting the register. */
#define ALT_SDMMC_RESP1_RESPONSE1_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_RESP1.
 */
struct ALT_SDMMC_RESP1_s
{
    const uint32_t  response1 : 32;  /* Response 1 */
};

/* The typedef declaration for register ALT_SDMMC_RESP1. */
typedef volatile struct ALT_SDMMC_RESP1_s  ALT_SDMMC_RESP1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_RESP1 register from the beginning of the component. */
#define ALT_SDMMC_RESP1_OFST        0x34

/*
 * Register : Response Register 2 - resp2
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [31:0] | R      | 0x0   | Response 2 
 * 
 */
/*
 * Field : Response 2 - response2
 * 
 * Bit[95:64] of long response
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RESP2_RESPONSE2 register field. */
#define ALT_SDMMC_RESP2_RESPONSE2_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RESP2_RESPONSE2 register field. */
#define ALT_SDMMC_RESP2_RESPONSE2_MSB        31
/* The width in bits of the ALT_SDMMC_RESP2_RESPONSE2 register field. */
#define ALT_SDMMC_RESP2_RESPONSE2_WIDTH      32
/* The mask used to set the ALT_SDMMC_RESP2_RESPONSE2 register field value. */
#define ALT_SDMMC_RESP2_RESPONSE2_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDMMC_RESP2_RESPONSE2 register field value. */
#define ALT_SDMMC_RESP2_RESPONSE2_CLR_MSK    0x00000000
/* The reset value of the ALT_SDMMC_RESP2_RESPONSE2 register field. */
#define ALT_SDMMC_RESP2_RESPONSE2_RESET      0x0
/* Extracts the ALT_SDMMC_RESP2_RESPONSE2 field value from a register. */
#define ALT_SDMMC_RESP2_RESPONSE2_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDMMC_RESP2_RESPONSE2 register field value suitable for setting the register. */
#define ALT_SDMMC_RESP2_RESPONSE2_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_RESP2.
 */
struct ALT_SDMMC_RESP2_s
{
    const uint32_t  response2 : 32;  /* Response 2 */
};

/* The typedef declaration for register ALT_SDMMC_RESP2. */
typedef volatile struct ALT_SDMMC_RESP2_s  ALT_SDMMC_RESP2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_RESP2 register from the beginning of the component. */
#define ALT_SDMMC_RESP2_OFST        0x38

/*
 * Register : Response Register 3 - resp3
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [31:0] | R      | 0x0   | Response 3 
 * 
 */
/*
 * Field : Response 3 - response3
 * 
 * Bit[127:96] of long response
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RESP3_RESPONSE3 register field. */
#define ALT_SDMMC_RESP3_RESPONSE3_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RESP3_RESPONSE3 register field. */
#define ALT_SDMMC_RESP3_RESPONSE3_MSB        31
/* The width in bits of the ALT_SDMMC_RESP3_RESPONSE3 register field. */
#define ALT_SDMMC_RESP3_RESPONSE3_WIDTH      32
/* The mask used to set the ALT_SDMMC_RESP3_RESPONSE3 register field value. */
#define ALT_SDMMC_RESP3_RESPONSE3_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDMMC_RESP3_RESPONSE3 register field value. */
#define ALT_SDMMC_RESP3_RESPONSE3_CLR_MSK    0x00000000
/* The reset value of the ALT_SDMMC_RESP3_RESPONSE3 register field. */
#define ALT_SDMMC_RESP3_RESPONSE3_RESET      0x0
/* Extracts the ALT_SDMMC_RESP3_RESPONSE3 field value from a register. */
#define ALT_SDMMC_RESP3_RESPONSE3_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDMMC_RESP3_RESPONSE3 register field value suitable for setting the register. */
#define ALT_SDMMC_RESP3_RESPONSE3_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_RESP3.
 */
struct ALT_SDMMC_RESP3_s
{
    const uint32_t  response3 : 32;  /* Response 3 */
};

/* The typedef declaration for register ALT_SDMMC_RESP3. */
typedef volatile struct ALT_SDMMC_RESP3_s  ALT_SDMMC_RESP3_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_RESP3 register from the beginning of the component. */
#define ALT_SDMMC_RESP3_OFST        0x3c

/*
 * Register : Masked Interrupt Status Register - mintsts
 * 
 * Describes state of Masked Interrupt Register.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                 
 * :--------|:-------|:------|:-----------------------------
 *  [0]     | R      | 0x0   | Card Detect                 
 *  [1]     | R      | 0x0   | Response Error              
 *  [2]     | R      | 0x0   | Command Done                
 *  [3]     | R      | 0x0   | Data Transfer Over          
 *  [4]     | R      | 0x0   | Data TX FIFO Data Request   
 *  [5]     | R      | 0x0   | Receive FIFO Data Request   
 *  [6]     | R      | 0x0   | Response CRC Error          
 *  [7]     | R      | 0x0   | Data CRC Error              
 *  [8]     | R      | 0x0   | Response Timeout            
 *  [9]     | R      | 0x0   | Data Read Timeout           
 *  [10]    | R      | 0x0   | Data Starvation Host Timeout
 *  [11]    | R      | 0x0   | FIFO Underrun Overrun Error 
 *  [12]    | R      | 0x0   | Hardware Locked Write Error 
 *  [13]    | R      | 0x0   | Start-bit Error             
 *  [14]    | R      | 0x0   | Auto Command Done           
 *  [15]    | R      | 0x0   | End-bit Error               
 *  [16]    | R      | 0x0   | SDIO Interrupts             
 *  [31:17] | ???    | 0x0   | *UNDEFINED*                 
 * 
 */
/*
 * Field : Card Detect - cd
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description          
 * :-----------------------------|:------|:----------------------
 *  ALT_SDMMC_MINTSTS_CD_E_MSK   | 0x0   | Card Detected Mask   
 *  ALT_SDMMC_MINTSTS_CD_E_NOMSK | 0x1   | Card Detected No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_CD
 * 
 * Card Detected Mask
 */
#define ALT_SDMMC_MINTSTS_CD_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_CD
 * 
 * Card Detected No Mask
 */
#define ALT_SDMMC_MINTSTS_CD_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_CD register field. */
#define ALT_SDMMC_MINTSTS_CD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_CD register field. */
#define ALT_SDMMC_MINTSTS_CD_MSB        0
/* The width in bits of the ALT_SDMMC_MINTSTS_CD register field. */
#define ALT_SDMMC_MINTSTS_CD_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_CD register field value. */
#define ALT_SDMMC_MINTSTS_CD_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_MINTSTS_CD register field value. */
#define ALT_SDMMC_MINTSTS_CD_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_MINTSTS_CD register field. */
#define ALT_SDMMC_MINTSTS_CD_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_CD field value from a register. */
#define ALT_SDMMC_MINTSTS_CD_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_MINTSTS_CD register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_CD_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Response Error - resp
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description           
 * :-------------------------------|:------|:-----------------------
 *  ALT_SDMMC_MINTSTS_RESP_E_MSK   | 0x0   | Response error Mask   
 *  ALT_SDMMC_MINTSTS_RESP_E_NOMSK | 0x1   | Response error No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_RESP
 * 
 * Response error Mask
 */
#define ALT_SDMMC_MINTSTS_RESP_E_MSK    0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_RESP
 * 
 * Response error No Mask
 */
#define ALT_SDMMC_MINTSTS_RESP_E_NOMSK  0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_RESP register field. */
#define ALT_SDMMC_MINTSTS_RESP_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_RESP register field. */
#define ALT_SDMMC_MINTSTS_RESP_MSB        1
/* The width in bits of the ALT_SDMMC_MINTSTS_RESP register field. */
#define ALT_SDMMC_MINTSTS_RESP_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_RESP register field value. */
#define ALT_SDMMC_MINTSTS_RESP_SET_MSK    0x00000002
/* The mask used to clear the ALT_SDMMC_MINTSTS_RESP register field value. */
#define ALT_SDMMC_MINTSTS_RESP_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SDMMC_MINTSTS_RESP register field. */
#define ALT_SDMMC_MINTSTS_RESP_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_RESP field value from a register. */
#define ALT_SDMMC_MINTSTS_RESP_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SDMMC_MINTSTS_RESP register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_RESP_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Command Done - cmd_done
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description         
 * :-----------------------------------|:------|:---------------------
 *  ALT_SDMMC_MINTSTS_CMD_DONE_E_MSK   | 0x0   | Command Done Mask   
 *  ALT_SDMMC_MINTSTS_CMD_DONE_E_NOMSK | 0x1   | Command Done No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_CMD_DONE
 * 
 * Command Done Mask
 */
#define ALT_SDMMC_MINTSTS_CMD_DONE_E_MSK    0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_CMD_DONE
 * 
 * Command Done No Mask
 */
#define ALT_SDMMC_MINTSTS_CMD_DONE_E_NOMSK  0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_CMD_DONE register field. */
#define ALT_SDMMC_MINTSTS_CMD_DONE_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_CMD_DONE register field. */
#define ALT_SDMMC_MINTSTS_CMD_DONE_MSB        2
/* The width in bits of the ALT_SDMMC_MINTSTS_CMD_DONE register field. */
#define ALT_SDMMC_MINTSTS_CMD_DONE_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_CMD_DONE register field value. */
#define ALT_SDMMC_MINTSTS_CMD_DONE_SET_MSK    0x00000004
/* The mask used to clear the ALT_SDMMC_MINTSTS_CMD_DONE register field value. */
#define ALT_SDMMC_MINTSTS_CMD_DONE_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SDMMC_MINTSTS_CMD_DONE register field. */
#define ALT_SDMMC_MINTSTS_CMD_DONE_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_CMD_DONE field value from a register. */
#define ALT_SDMMC_MINTSTS_CMD_DONE_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SDMMC_MINTSTS_CMD_DONE register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_CMD_DONE_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Data Transfer Over - dt
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description               
 * :-----------------------------|:------|:---------------------------
 *  ALT_SDMMC_MINTSTS_DT_E_MSK   | 0x0   | Data transfer over Mask   
 *  ALT_SDMMC_MINTSTS_DT_E_NOMSK | 0x1   | Data transfer over No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_DT
 * 
 * Data transfer over Mask
 */
#define ALT_SDMMC_MINTSTS_DT_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_DT
 * 
 * Data transfer over No Mask
 */
#define ALT_SDMMC_MINTSTS_DT_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_DT register field. */
#define ALT_SDMMC_MINTSTS_DT_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_DT register field. */
#define ALT_SDMMC_MINTSTS_DT_MSB        3
/* The width in bits of the ALT_SDMMC_MINTSTS_DT register field. */
#define ALT_SDMMC_MINTSTS_DT_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_DT register field value. */
#define ALT_SDMMC_MINTSTS_DT_SET_MSK    0x00000008
/* The mask used to clear the ALT_SDMMC_MINTSTS_DT register field value. */
#define ALT_SDMMC_MINTSTS_DT_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SDMMC_MINTSTS_DT register field. */
#define ALT_SDMMC_MINTSTS_DT_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_DT field value from a register. */
#define ALT_SDMMC_MINTSTS_DT_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SDMMC_MINTSTS_DT register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_DT_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Data TX FIFO Data Request - dttxfifodr
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description                       
 * :-------------------------------------|:------|:-----------------------------------
 *  ALT_SDMMC_MINTSTS_DTTXFIFODR_E_MSK   | 0x0   | Transmit FIFO data request Mask   
 *  ALT_SDMMC_MINTSTS_DTTXFIFODR_E_NOMSK | 0x1   | Transmit FIFO data request No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_DTTXFIFODR
 * 
 * Transmit FIFO data request Mask
 */
#define ALT_SDMMC_MINTSTS_DTTXFIFODR_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_DTTXFIFODR
 * 
 * Transmit FIFO data request No Mask
 */
#define ALT_SDMMC_MINTSTS_DTTXFIFODR_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_DTTXFIFODR register field. */
#define ALT_SDMMC_MINTSTS_DTTXFIFODR_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_DTTXFIFODR register field. */
#define ALT_SDMMC_MINTSTS_DTTXFIFODR_MSB        4
/* The width in bits of the ALT_SDMMC_MINTSTS_DTTXFIFODR register field. */
#define ALT_SDMMC_MINTSTS_DTTXFIFODR_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_DTTXFIFODR register field value. */
#define ALT_SDMMC_MINTSTS_DTTXFIFODR_SET_MSK    0x00000010
/* The mask used to clear the ALT_SDMMC_MINTSTS_DTTXFIFODR register field value. */
#define ALT_SDMMC_MINTSTS_DTTXFIFODR_CLR_MSK    0xffffffef
/* The reset value of the ALT_SDMMC_MINTSTS_DTTXFIFODR register field. */
#define ALT_SDMMC_MINTSTS_DTTXFIFODR_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_DTTXFIFODR field value from a register. */
#define ALT_SDMMC_MINTSTS_DTTXFIFODR_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SDMMC_MINTSTS_DTTXFIFODR register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_DTTXFIFODR_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Receive FIFO Data Request - rxfifodr
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                      
 * :-----------------------------------|:------|:----------------------------------
 *  ALT_SDMMC_MINTSTS_RXFIFODR_E_MSK   | 0x0   | Receive FIFO data request Mask   
 *  ALT_SDMMC_MINTSTS_RXFIFODR_E_NOMSK | 0x1   | Receive FIFO data request No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_RXFIFODR
 * 
 * Receive FIFO data request Mask
 */
#define ALT_SDMMC_MINTSTS_RXFIFODR_E_MSK    0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_RXFIFODR
 * 
 * Receive FIFO data request No Mask
 */
#define ALT_SDMMC_MINTSTS_RXFIFODR_E_NOMSK  0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_RXFIFODR register field. */
#define ALT_SDMMC_MINTSTS_RXFIFODR_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_RXFIFODR register field. */
#define ALT_SDMMC_MINTSTS_RXFIFODR_MSB        5
/* The width in bits of the ALT_SDMMC_MINTSTS_RXFIFODR register field. */
#define ALT_SDMMC_MINTSTS_RXFIFODR_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_RXFIFODR register field value. */
#define ALT_SDMMC_MINTSTS_RXFIFODR_SET_MSK    0x00000020
/* The mask used to clear the ALT_SDMMC_MINTSTS_RXFIFODR register field value. */
#define ALT_SDMMC_MINTSTS_RXFIFODR_CLR_MSK    0xffffffdf
/* The reset value of the ALT_SDMMC_MINTSTS_RXFIFODR register field. */
#define ALT_SDMMC_MINTSTS_RXFIFODR_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_RXFIFODR field value from a register. */
#define ALT_SDMMC_MINTSTS_RXFIFODR_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_SDMMC_MINTSTS_RXFIFODR register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_RXFIFODR_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Response CRC Error - respcrcerr
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description               
 * :-------------------------------------|:------|:---------------------------
 *  ALT_SDMMC_MINTSTS_RESPCRCERR_E_MSK   | 0x0   | Response CRC error Mask   
 *  ALT_SDMMC_MINTSTS_RESPCRCERR_E_NOMSK | 0x1   | Response CRC error No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_RESPCRCERR
 * 
 * Response CRC error Mask
 */
#define ALT_SDMMC_MINTSTS_RESPCRCERR_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_RESPCRCERR
 * 
 * Response CRC error No Mask
 */
#define ALT_SDMMC_MINTSTS_RESPCRCERR_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_RESPCRCERR register field. */
#define ALT_SDMMC_MINTSTS_RESPCRCERR_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_RESPCRCERR register field. */
#define ALT_SDMMC_MINTSTS_RESPCRCERR_MSB        6
/* The width in bits of the ALT_SDMMC_MINTSTS_RESPCRCERR register field. */
#define ALT_SDMMC_MINTSTS_RESPCRCERR_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_RESPCRCERR register field value. */
#define ALT_SDMMC_MINTSTS_RESPCRCERR_SET_MSK    0x00000040
/* The mask used to clear the ALT_SDMMC_MINTSTS_RESPCRCERR register field value. */
#define ALT_SDMMC_MINTSTS_RESPCRCERR_CLR_MSK    0xffffffbf
/* The reset value of the ALT_SDMMC_MINTSTS_RESPCRCERR register field. */
#define ALT_SDMMC_MINTSTS_RESPCRCERR_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_RESPCRCERR field value from a register. */
#define ALT_SDMMC_MINTSTS_RESPCRCERR_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_SDMMC_MINTSTS_RESPCRCERR register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_RESPCRCERR_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Data CRC Error - datacrcerr
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description           
 * :-------------------------------------|:------|:-----------------------
 *  ALT_SDMMC_MINTSTS_DATACRCERR_E_MSK   | 0x0   | Data CRC error Mask   
 *  ALT_SDMMC_MINTSTS_DATACRCERR_E_NOMSK | 0x1   | Data CRC error No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_DATACRCERR
 * 
 * Data CRC error Mask
 */
#define ALT_SDMMC_MINTSTS_DATACRCERR_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_DATACRCERR
 * 
 * Data CRC error No Mask
 */
#define ALT_SDMMC_MINTSTS_DATACRCERR_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_DATACRCERR register field. */
#define ALT_SDMMC_MINTSTS_DATACRCERR_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_DATACRCERR register field. */
#define ALT_SDMMC_MINTSTS_DATACRCERR_MSB        7
/* The width in bits of the ALT_SDMMC_MINTSTS_DATACRCERR register field. */
#define ALT_SDMMC_MINTSTS_DATACRCERR_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_DATACRCERR register field value. */
#define ALT_SDMMC_MINTSTS_DATACRCERR_SET_MSK    0x00000080
/* The mask used to clear the ALT_SDMMC_MINTSTS_DATACRCERR register field value. */
#define ALT_SDMMC_MINTSTS_DATACRCERR_CLR_MSK    0xffffff7f
/* The reset value of the ALT_SDMMC_MINTSTS_DATACRCERR register field. */
#define ALT_SDMMC_MINTSTS_DATACRCERR_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_DATACRCERR field value from a register. */
#define ALT_SDMMC_MINTSTS_DATACRCERR_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_SDMMC_MINTSTS_DATACRCERR register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_DATACRCERR_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Response Timeout - respto
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description             
 * :---------------------------------|:------|:-------------------------
 *  ALT_SDMMC_MINTSTS_RESPTO_E_MSK   | 0x0   | Response timeout Mask   
 *  ALT_SDMMC_MINTSTS_RESPTO_E_NOMSK | 0x1   | Response timeout No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_RESPTO
 * 
 * Response timeout Mask
 */
#define ALT_SDMMC_MINTSTS_RESPTO_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_RESPTO
 * 
 * Response timeout No Mask
 */
#define ALT_SDMMC_MINTSTS_RESPTO_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_RESPTO register field. */
#define ALT_SDMMC_MINTSTS_RESPTO_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_RESPTO register field. */
#define ALT_SDMMC_MINTSTS_RESPTO_MSB        8
/* The width in bits of the ALT_SDMMC_MINTSTS_RESPTO register field. */
#define ALT_SDMMC_MINTSTS_RESPTO_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_RESPTO register field value. */
#define ALT_SDMMC_MINTSTS_RESPTO_SET_MSK    0x00000100
/* The mask used to clear the ALT_SDMMC_MINTSTS_RESPTO register field value. */
#define ALT_SDMMC_MINTSTS_RESPTO_CLR_MSK    0xfffffeff
/* The reset value of the ALT_SDMMC_MINTSTS_RESPTO register field. */
#define ALT_SDMMC_MINTSTS_RESPTO_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_RESPTO field value from a register. */
#define ALT_SDMMC_MINTSTS_RESPTO_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_SDMMC_MINTSTS_RESPTO register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_RESPTO_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Data Read Timeout - datardto
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description              
 * :-----------------------------------|:------|:--------------------------
 *  ALT_SDMMC_MINTSTS_DATARDTO_E_MSK   | 0x0   | Data read timeout Mask   
 *  ALT_SDMMC_MINTSTS_DATARDTO_E_NOMSK | 0x1   | Data read timeout No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_DATARDTO
 * 
 * Data read timeout Mask
 */
#define ALT_SDMMC_MINTSTS_DATARDTO_E_MSK    0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_DATARDTO
 * 
 * Data read timeout No Mask
 */
#define ALT_SDMMC_MINTSTS_DATARDTO_E_NOMSK  0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_DATARDTO register field. */
#define ALT_SDMMC_MINTSTS_DATARDTO_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_DATARDTO register field. */
#define ALT_SDMMC_MINTSTS_DATARDTO_MSB        9
/* The width in bits of the ALT_SDMMC_MINTSTS_DATARDTO register field. */
#define ALT_SDMMC_MINTSTS_DATARDTO_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_DATARDTO register field value. */
#define ALT_SDMMC_MINTSTS_DATARDTO_SET_MSK    0x00000200
/* The mask used to clear the ALT_SDMMC_MINTSTS_DATARDTO register field value. */
#define ALT_SDMMC_MINTSTS_DATARDTO_CLR_MSK    0xfffffdff
/* The reset value of the ALT_SDMMC_MINTSTS_DATARDTO register field. */
#define ALT_SDMMC_MINTSTS_DATARDTO_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_DATARDTO field value from a register. */
#define ALT_SDMMC_MINTSTS_DATARDTO_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_SDMMC_MINTSTS_DATARDTO register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_DATARDTO_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Data Starvation Host Timeout - dshto
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description                            
 * :--------------------------------|:------|:----------------------------------------
 *  ALT_SDMMC_MINTSTS_DSHTO_E_MSK   | 0x0   | Data starvation by host timeout Mask   
 *  ALT_SDMMC_MINTSTS_DSHTO_E_NOMSK | 0x1   | Data starvation by host timeout No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_DSHTO
 * 
 * Data starvation by host timeout Mask
 */
#define ALT_SDMMC_MINTSTS_DSHTO_E_MSK   0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_DSHTO
 * 
 * Data starvation by host timeout No Mask
 */
#define ALT_SDMMC_MINTSTS_DSHTO_E_NOMSK 0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_DSHTO register field. */
#define ALT_SDMMC_MINTSTS_DSHTO_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_DSHTO register field. */
#define ALT_SDMMC_MINTSTS_DSHTO_MSB        10
/* The width in bits of the ALT_SDMMC_MINTSTS_DSHTO register field. */
#define ALT_SDMMC_MINTSTS_DSHTO_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_DSHTO register field value. */
#define ALT_SDMMC_MINTSTS_DSHTO_SET_MSK    0x00000400
/* The mask used to clear the ALT_SDMMC_MINTSTS_DSHTO register field value. */
#define ALT_SDMMC_MINTSTS_DSHTO_CLR_MSK    0xfffffbff
/* The reset value of the ALT_SDMMC_MINTSTS_DSHTO register field. */
#define ALT_SDMMC_MINTSTS_DSHTO_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_DSHTO field value from a register. */
#define ALT_SDMMC_MINTSTS_DSHTO_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_SDMMC_MINTSTS_DSHTO register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_DSHTO_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : FIFO Underrun Overrun Error - fifoovunerr
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description                        
 * :--------------------------------------|:------|:------------------------------------
 *  ALT_SDMMC_MINTSTS_FIFOOVUNERR_E_MSK   | 0x0   | FIFO underrun/overrun error Mask   
 *  ALT_SDMMC_MINTSTS_FIFOOVUNERR_E_NOMSK | 0x1   | FIFO underrun/overrun error No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_FIFOOVUNERR
 * 
 * FIFO underrun/overrun error Mask
 */
#define ALT_SDMMC_MINTSTS_FIFOOVUNERR_E_MSK     0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_FIFOOVUNERR
 * 
 * FIFO underrun/overrun error No Mask
 */
#define ALT_SDMMC_MINTSTS_FIFOOVUNERR_E_NOMSK   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_FIFOOVUNERR register field. */
#define ALT_SDMMC_MINTSTS_FIFOOVUNERR_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_FIFOOVUNERR register field. */
#define ALT_SDMMC_MINTSTS_FIFOOVUNERR_MSB        11
/* The width in bits of the ALT_SDMMC_MINTSTS_FIFOOVUNERR register field. */
#define ALT_SDMMC_MINTSTS_FIFOOVUNERR_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_FIFOOVUNERR register field value. */
#define ALT_SDMMC_MINTSTS_FIFOOVUNERR_SET_MSK    0x00000800
/* The mask used to clear the ALT_SDMMC_MINTSTS_FIFOOVUNERR register field value. */
#define ALT_SDMMC_MINTSTS_FIFOOVUNERR_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_SDMMC_MINTSTS_FIFOOVUNERR register field. */
#define ALT_SDMMC_MINTSTS_FIFOOVUNERR_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_FIFOOVUNERR field value from a register. */
#define ALT_SDMMC_MINTSTS_FIFOOVUNERR_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_SDMMC_MINTSTS_FIFOOVUNERR register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_FIFOOVUNERR_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : Hardware Locked Write Error - hlwerr
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                        
 * :---------------------------------|:------|:------------------------------------
 *  ALT_SDMMC_MINTSTS_HLWERR_E_MSK   | 0x0   | Hardware locked write error Mask   
 *  ALT_SDMMC_MINTSTS_HLWERR_E_NOMSK | 0x1   | Hardware locked write error No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_HLWERR
 * 
 * Hardware locked write error Mask
 */
#define ALT_SDMMC_MINTSTS_HLWERR_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_HLWERR
 * 
 * Hardware locked write error No Mask
 */
#define ALT_SDMMC_MINTSTS_HLWERR_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_HLWERR register field. */
#define ALT_SDMMC_MINTSTS_HLWERR_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_HLWERR register field. */
#define ALT_SDMMC_MINTSTS_HLWERR_MSB        12
/* The width in bits of the ALT_SDMMC_MINTSTS_HLWERR register field. */
#define ALT_SDMMC_MINTSTS_HLWERR_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_HLWERR register field value. */
#define ALT_SDMMC_MINTSTS_HLWERR_SET_MSK    0x00001000
/* The mask used to clear the ALT_SDMMC_MINTSTS_HLWERR register field value. */
#define ALT_SDMMC_MINTSTS_HLWERR_CLR_MSK    0xffffefff
/* The reset value of the ALT_SDMMC_MINTSTS_HLWERR register field. */
#define ALT_SDMMC_MINTSTS_HLWERR_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_HLWERR field value from a register. */
#define ALT_SDMMC_MINTSTS_HLWERR_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_SDMMC_MINTSTS_HLWERR register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_HLWERR_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : Start-bit Error - strerr
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description            
 * :---------------------------------|:------|:------------------------
 *  ALT_SDMMC_MINTSTS_STRERR_E_MSK   | 0x0   | Start-bit error Mask   
 *  ALT_SDMMC_MINTSTS_STRERR_E_NOMSK | 0x1   | Start-bit error No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_STRERR
 * 
 * Start-bit error Mask
 */
#define ALT_SDMMC_MINTSTS_STRERR_E_MSK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_STRERR
 * 
 * Start-bit error No Mask
 */
#define ALT_SDMMC_MINTSTS_STRERR_E_NOMSK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_STRERR register field. */
#define ALT_SDMMC_MINTSTS_STRERR_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_STRERR register field. */
#define ALT_SDMMC_MINTSTS_STRERR_MSB        13
/* The width in bits of the ALT_SDMMC_MINTSTS_STRERR register field. */
#define ALT_SDMMC_MINTSTS_STRERR_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_STRERR register field value. */
#define ALT_SDMMC_MINTSTS_STRERR_SET_MSK    0x00002000
/* The mask used to clear the ALT_SDMMC_MINTSTS_STRERR register field value. */
#define ALT_SDMMC_MINTSTS_STRERR_CLR_MSK    0xffffdfff
/* The reset value of the ALT_SDMMC_MINTSTS_STRERR register field. */
#define ALT_SDMMC_MINTSTS_STRERR_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_STRERR field value from a register. */
#define ALT_SDMMC_MINTSTS_STRERR_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_SDMMC_MINTSTS_STRERR register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_STRERR_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : Auto Command Done - acd
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description              
 * :------------------------------|:------|:--------------------------
 *  ALT_SDMMC_MINTSTS_ACD_E_MSK   | 0x0   | Auto command done Mask   
 *  ALT_SDMMC_MINTSTS_ACD_E_NOMSK | 0x1   | Auto command done No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_ACD
 * 
 * Auto command done Mask
 */
#define ALT_SDMMC_MINTSTS_ACD_E_MSK     0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_ACD
 * 
 * Auto command done No Mask
 */
#define ALT_SDMMC_MINTSTS_ACD_E_NOMSK   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_ACD register field. */
#define ALT_SDMMC_MINTSTS_ACD_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_ACD register field. */
#define ALT_SDMMC_MINTSTS_ACD_MSB        14
/* The width in bits of the ALT_SDMMC_MINTSTS_ACD register field. */
#define ALT_SDMMC_MINTSTS_ACD_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_ACD register field value. */
#define ALT_SDMMC_MINTSTS_ACD_SET_MSK    0x00004000
/* The mask used to clear the ALT_SDMMC_MINTSTS_ACD register field value. */
#define ALT_SDMMC_MINTSTS_ACD_CLR_MSK    0xffffbfff
/* The reset value of the ALT_SDMMC_MINTSTS_ACD register field. */
#define ALT_SDMMC_MINTSTS_ACD_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_ACD field value from a register. */
#define ALT_SDMMC_MINTSTS_ACD_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_SDMMC_MINTSTS_ACD register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_ACD_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : End-bit Error - ebe
 * 
 * Interrupt enabled only if corresponding bit in interrupt mask register is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description          
 * :------------------------------|:------|:----------------------
 *  ALT_SDMMC_MINTSTS_EBE_E_MSK   | 0x0   | End-bit error Mask   
 *  ALT_SDMMC_MINTSTS_EBE_E_NOMSK | 0x1   | End-bit error No Mask
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_EBE
 * 
 * End-bit error Mask
 */
#define ALT_SDMMC_MINTSTS_EBE_E_MSK     0x0
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_EBE
 * 
 * End-bit error No Mask
 */
#define ALT_SDMMC_MINTSTS_EBE_E_NOMSK   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_EBE register field. */
#define ALT_SDMMC_MINTSTS_EBE_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_EBE register field. */
#define ALT_SDMMC_MINTSTS_EBE_MSB        15
/* The width in bits of the ALT_SDMMC_MINTSTS_EBE register field. */
#define ALT_SDMMC_MINTSTS_EBE_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_EBE register field value. */
#define ALT_SDMMC_MINTSTS_EBE_SET_MSK    0x00008000
/* The mask used to clear the ALT_SDMMC_MINTSTS_EBE register field value. */
#define ALT_SDMMC_MINTSTS_EBE_CLR_MSK    0xffff7fff
/* The reset value of the ALT_SDMMC_MINTSTS_EBE register field. */
#define ALT_SDMMC_MINTSTS_EBE_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_EBE field value from a register. */
#define ALT_SDMMC_MINTSTS_EBE_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_SDMMC_MINTSTS_EBE register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_EBE_SET(value) (((value) << 15) & 0x00008000)

/*
 * Field : SDIO Interrupts - sdio_interrupt
 * 
 * Interrupt from SDIO card: one bit for each card. Bit[16] is for Card[0]. SDIO
 * interrupt for card enabled only if corresponding sdio_int_mask bit is set in
 * Interrupt mask register (mask bit 1 enables interrupt; 0 masks interrupt). In
 * MMC-Ver3.3-only mode, bits always 0.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                
 * :-----------------------------------|:------|:----------------------------
 *  ALT_SDMMC_MINTSTS_SDIO_INT_E_ACT   | 0x1   | SDIO interrupt from card   
 *  ALT_SDMMC_MINTSTS_SDIO_INT_E_INACT | 0x0   | No SDIO interrupt from card
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_SDIO_INT
 * 
 * SDIO interrupt from card
 */
#define ALT_SDMMC_MINTSTS_SDIO_INT_E_ACT    0x1
/*
 * Enumerated value for register field ALT_SDMMC_MINTSTS_SDIO_INT
 * 
 * No SDIO interrupt from card
 */
#define ALT_SDMMC_MINTSTS_SDIO_INT_E_INACT  0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_MINTSTS_SDIO_INT register field. */
#define ALT_SDMMC_MINTSTS_SDIO_INT_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_MINTSTS_SDIO_INT register field. */
#define ALT_SDMMC_MINTSTS_SDIO_INT_MSB        16
/* The width in bits of the ALT_SDMMC_MINTSTS_SDIO_INT register field. */
#define ALT_SDMMC_MINTSTS_SDIO_INT_WIDTH      1
/* The mask used to set the ALT_SDMMC_MINTSTS_SDIO_INT register field value. */
#define ALT_SDMMC_MINTSTS_SDIO_INT_SET_MSK    0x00010000
/* The mask used to clear the ALT_SDMMC_MINTSTS_SDIO_INT register field value. */
#define ALT_SDMMC_MINTSTS_SDIO_INT_CLR_MSK    0xfffeffff
/* The reset value of the ALT_SDMMC_MINTSTS_SDIO_INT register field. */
#define ALT_SDMMC_MINTSTS_SDIO_INT_RESET      0x0
/* Extracts the ALT_SDMMC_MINTSTS_SDIO_INT field value from a register. */
#define ALT_SDMMC_MINTSTS_SDIO_INT_GET(value) (((value) & 0x00010000) >> 16)
/* Produces a ALT_SDMMC_MINTSTS_SDIO_INT register field value suitable for setting the register. */
#define ALT_SDMMC_MINTSTS_SDIO_INT_SET(value) (((value) << 16) & 0x00010000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_MINTSTS.
 */
struct ALT_SDMMC_MINTSTS_s
{
    const uint32_t  cd             :  1;  /* Card Detect */
    const uint32_t  resp           :  1;  /* Response Error */
    const uint32_t  cmd_done       :  1;  /* Command Done */
    const uint32_t  dt             :  1;  /* Data Transfer Over */
    const uint32_t  dttxfifodr     :  1;  /* Data TX FIFO Data Request */
    const uint32_t  rxfifodr       :  1;  /* Receive FIFO Data Request */
    const uint32_t  respcrcerr     :  1;  /* Response CRC Error */
    const uint32_t  datacrcerr     :  1;  /* Data CRC Error */
    const uint32_t  respto         :  1;  /* Response Timeout */
    const uint32_t  datardto       :  1;  /* Data Read Timeout */
    const uint32_t  dshto          :  1;  /* Data Starvation Host Timeout */
    const uint32_t  fifoovunerr    :  1;  /* FIFO Underrun Overrun Error */
    const uint32_t  hlwerr         :  1;  /* Hardware Locked Write Error */
    const uint32_t  strerr         :  1;  /* Start-bit Error */
    const uint32_t  acd            :  1;  /* Auto Command Done */
    const uint32_t  ebe            :  1;  /* End-bit Error */
    const uint32_t  sdio_interrupt :  1;  /* SDIO Interrupts */
    uint32_t                       : 15;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_MINTSTS. */
typedef volatile struct ALT_SDMMC_MINTSTS_s  ALT_SDMMC_MINTSTS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_MINTSTS register from the beginning of the component. */
#define ALT_SDMMC_MINTSTS_OFST        0x40

/*
 * Register : Raw Interrupt Status Register - rintsts
 * 
 * Interrupt Status Before Masking.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                 
 * :--------|:-------|:------|:---------------------------------------------
 *  [0]     | RW     | 0x0   | Card Detect                                 
 *  [1]     | RW     | 0x0   | Response Error                              
 *  [2]     | RW     | 0x0   | Command Done                                
 *  [3]     | RW     | 0x0   | Data Transfer Over                          
 *  [4]     | RW     | 0x0   | Transmit FIFO Data Request                  
 *  [5]     | RW     | 0x0   | Receive FIFO Data Request                   
 *  [6]     | RW     | 0x0   | Response CRC Error                          
 *  [7]     | RW     | 0x0   | Data CRC Error                              
 *  [8]     | RW     | 0x0   | Response Timeout Boot Ack Received          
 *  [9]     | RW     | 0x0   | Data Read Timeout Boot Data Start           
 *  [10]    | RW     | 0x0   | Data Starvation Host Timeout Volt Switch_int
 *  [11]    | RW     | 0x0   | FIFO Underrun Overrun Error                 
 *  [12]    | RW     | 0x0   | Hardware Locked Write Error                 
 *  [13]    | RW     | 0x0   | Start-bit error (SBE)                       
 *  [14]    | RW     | 0x0   | Auto Cmommand Done                          
 *  [15]    | RW     | 0x0   | End-bit Error                               
 *  [16]    | RW     | 0x0   | SDIO Interrupt                              
 *  [31:17] | ???    | 0x0   | *UNDEFINED*                                 
 * 
 */
/*
 * Field : Card Detect - cd
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description            
 * :-----------------------------|:------|:------------------------
 *  ALT_SDMMC_RINTSTS_CD_E_INACT | 0x0   | Card detect (CD)       
 *  ALT_SDMMC_RINTSTS_CD_E_ACT   | 0x1   | Clears Card detect (CD)
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_CD
 * 
 * Card detect (CD)
 */
#define ALT_SDMMC_RINTSTS_CD_E_INACT    0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_CD
 * 
 * Clears Card detect (CD)
 */
#define ALT_SDMMC_RINTSTS_CD_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_CD register field. */
#define ALT_SDMMC_RINTSTS_CD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_CD register field. */
#define ALT_SDMMC_RINTSTS_CD_MSB        0
/* The width in bits of the ALT_SDMMC_RINTSTS_CD register field. */
#define ALT_SDMMC_RINTSTS_CD_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_CD register field value. */
#define ALT_SDMMC_RINTSTS_CD_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_RINTSTS_CD register field value. */
#define ALT_SDMMC_RINTSTS_CD_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_RINTSTS_CD register field. */
#define ALT_SDMMC_RINTSTS_CD_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_CD field value from a register. */
#define ALT_SDMMC_RINTSTS_CD_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_RINTSTS_CD register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_CD_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Response Error - re
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description               
 * :-----------------------------|:------|:---------------------------
 *  ALT_SDMMC_RINTSTS_RE_E_INACT | 0x0   | Response error (RE)       
 *  ALT_SDMMC_RINTSTS_RE_E_ACT   | 0x1   | Clears Response error (RE)
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_RE
 * 
 * Response error (RE)
 */
#define ALT_SDMMC_RINTSTS_RE_E_INACT    0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_RE
 * 
 * Clears Response error (RE)
 */
#define ALT_SDMMC_RINTSTS_RE_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_RE register field. */
#define ALT_SDMMC_RINTSTS_RE_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_RE register field. */
#define ALT_SDMMC_RINTSTS_RE_MSB        1
/* The width in bits of the ALT_SDMMC_RINTSTS_RE register field. */
#define ALT_SDMMC_RINTSTS_RE_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_RE register field value. */
#define ALT_SDMMC_RINTSTS_RE_SET_MSK    0x00000002
/* The mask used to clear the ALT_SDMMC_RINTSTS_RE register field value. */
#define ALT_SDMMC_RINTSTS_RE_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SDMMC_RINTSTS_RE register field. */
#define ALT_SDMMC_RINTSTS_RE_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_RE field value from a register. */
#define ALT_SDMMC_RINTSTS_RE_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SDMMC_RINTSTS_RE register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_RE_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Command Done - cmd
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description             
 * :------------------------------|:------|:-------------------------
 *  ALT_SDMMC_RINTSTS_CMD_E_INACT | 0x0   | Command done (CD)       
 *  ALT_SDMMC_RINTSTS_CMD_E_ACT   | 0x1   | Clears Command done (CD)
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_CMD
 * 
 * Command done (CD)
 */
#define ALT_SDMMC_RINTSTS_CMD_E_INACT   0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_CMD
 * 
 * Clears Command done (CD)
 */
#define ALT_SDMMC_RINTSTS_CMD_E_ACT     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_CMD register field. */
#define ALT_SDMMC_RINTSTS_CMD_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_CMD register field. */
#define ALT_SDMMC_RINTSTS_CMD_MSB        2
/* The width in bits of the ALT_SDMMC_RINTSTS_CMD register field. */
#define ALT_SDMMC_RINTSTS_CMD_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_CMD register field value. */
#define ALT_SDMMC_RINTSTS_CMD_SET_MSK    0x00000004
/* The mask used to clear the ALT_SDMMC_RINTSTS_CMD register field value. */
#define ALT_SDMMC_RINTSTS_CMD_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SDMMC_RINTSTS_CMD register field. */
#define ALT_SDMMC_RINTSTS_CMD_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_CMD field value from a register. */
#define ALT_SDMMC_RINTSTS_CMD_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SDMMC_RINTSTS_CMD register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_CMD_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Data Transfer Over - dto
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                    
 * :------------------------------|:------|:--------------------------------
 *  ALT_SDMMC_RINTSTS_DTO_E_INACT | 0x0   | Data transfer over (DTO)       
 *  ALT_SDMMC_RINTSTS_DTO_E_ACT   | 0x1   | Clears Data transfer over (DTO)
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_DTO
 * 
 * Data transfer over (DTO)
 */
#define ALT_SDMMC_RINTSTS_DTO_E_INACT   0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_DTO
 * 
 * Clears Data transfer over (DTO)
 */
#define ALT_SDMMC_RINTSTS_DTO_E_ACT     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_DTO register field. */
#define ALT_SDMMC_RINTSTS_DTO_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_DTO register field. */
#define ALT_SDMMC_RINTSTS_DTO_MSB        3
/* The width in bits of the ALT_SDMMC_RINTSTS_DTO register field. */
#define ALT_SDMMC_RINTSTS_DTO_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_DTO register field value. */
#define ALT_SDMMC_RINTSTS_DTO_SET_MSK    0x00000008
/* The mask used to clear the ALT_SDMMC_RINTSTS_DTO register field value. */
#define ALT_SDMMC_RINTSTS_DTO_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SDMMC_RINTSTS_DTO register field. */
#define ALT_SDMMC_RINTSTS_DTO_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_DTO field value from a register. */
#define ALT_SDMMC_RINTSTS_DTO_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SDMMC_RINTSTS_DTO register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_DTO_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Transmit FIFO Data Request - txdr
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description                             
 * :-------------------------------|:------|:-----------------------------------------
 *  ALT_SDMMC_RINTSTS_TXDR_E_INACT | 0x0   | Transmit FIFO data request (TXDR)       
 *  ALT_SDMMC_RINTSTS_TXDR_E_ACT   | 0x1   | Clears Transmit FIFO data request (TXDR)
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_TXDR
 * 
 * Transmit FIFO data request (TXDR)
 */
#define ALT_SDMMC_RINTSTS_TXDR_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_TXDR
 * 
 * Clears Transmit FIFO data request (TXDR)
 */
#define ALT_SDMMC_RINTSTS_TXDR_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_TXDR register field. */
#define ALT_SDMMC_RINTSTS_TXDR_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_TXDR register field. */
#define ALT_SDMMC_RINTSTS_TXDR_MSB        4
/* The width in bits of the ALT_SDMMC_RINTSTS_TXDR register field. */
#define ALT_SDMMC_RINTSTS_TXDR_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_TXDR register field value. */
#define ALT_SDMMC_RINTSTS_TXDR_SET_MSK    0x00000010
/* The mask used to clear the ALT_SDMMC_RINTSTS_TXDR register field value. */
#define ALT_SDMMC_RINTSTS_TXDR_CLR_MSK    0xffffffef
/* The reset value of the ALT_SDMMC_RINTSTS_TXDR register field. */
#define ALT_SDMMC_RINTSTS_TXDR_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_TXDR field value from a register. */
#define ALT_SDMMC_RINTSTS_TXDR_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SDMMC_RINTSTS_TXDR register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_TXDR_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Receive FIFO Data Request - rxdr
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description                            
 * :-------------------------------|:------|:----------------------------------------
 *  ALT_SDMMC_RINTSTS_RXDR_E_INACT | 0x0   | Receive FIFO data request (RXDR)       
 *  ALT_SDMMC_RINTSTS_RXDR_E_ACT   | 0x1   | Clears Receive FIFO data request (RXDR)
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_RXDR
 * 
 * Receive FIFO data request (RXDR)
 */
#define ALT_SDMMC_RINTSTS_RXDR_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_RXDR
 * 
 * Clears Receive FIFO data request (RXDR)
 */
#define ALT_SDMMC_RINTSTS_RXDR_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_RXDR register field. */
#define ALT_SDMMC_RINTSTS_RXDR_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_RXDR register field. */
#define ALT_SDMMC_RINTSTS_RXDR_MSB        5
/* The width in bits of the ALT_SDMMC_RINTSTS_RXDR register field. */
#define ALT_SDMMC_RINTSTS_RXDR_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_RXDR register field value. */
#define ALT_SDMMC_RINTSTS_RXDR_SET_MSK    0x00000020
/* The mask used to clear the ALT_SDMMC_RINTSTS_RXDR register field value. */
#define ALT_SDMMC_RINTSTS_RXDR_CLR_MSK    0xffffffdf
/* The reset value of the ALT_SDMMC_RINTSTS_RXDR register field. */
#define ALT_SDMMC_RINTSTS_RXDR_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_RXDR field value from a register. */
#define ALT_SDMMC_RINTSTS_RXDR_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_SDMMC_RINTSTS_RXDR register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_RXDR_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Response CRC Error - rcrc
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description                     
 * :-------------------------------|:------|:---------------------------------
 *  ALT_SDMMC_RINTSTS_RCRC_E_INACT | 0x0   | Response CRC error (RCRC)       
 *  ALT_SDMMC_RINTSTS_RCRC_E_ACT   | 0x1   | Clears Response CRC error (RCRC)
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_RCRC
 * 
 * Response CRC error (RCRC)
 */
#define ALT_SDMMC_RINTSTS_RCRC_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_RCRC
 * 
 * Clears Response CRC error (RCRC)
 */
#define ALT_SDMMC_RINTSTS_RCRC_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_RCRC register field. */
#define ALT_SDMMC_RINTSTS_RCRC_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_RCRC register field. */
#define ALT_SDMMC_RINTSTS_RCRC_MSB        6
/* The width in bits of the ALT_SDMMC_RINTSTS_RCRC register field. */
#define ALT_SDMMC_RINTSTS_RCRC_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_RCRC register field value. */
#define ALT_SDMMC_RINTSTS_RCRC_SET_MSK    0x00000040
/* The mask used to clear the ALT_SDMMC_RINTSTS_RCRC register field value. */
#define ALT_SDMMC_RINTSTS_RCRC_CLR_MSK    0xffffffbf
/* The reset value of the ALT_SDMMC_RINTSTS_RCRC register field. */
#define ALT_SDMMC_RINTSTS_RCRC_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_RCRC field value from a register. */
#define ALT_SDMMC_RINTSTS_RCRC_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_SDMMC_RINTSTS_RCRC register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_RCRC_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Data CRC Error - dcrc
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description                 
 * :-------------------------------|:------|:-----------------------------
 *  ALT_SDMMC_RINTSTS_DCRC_E_INACT | 0x0   | Data CRC error (DCRC)       
 *  ALT_SDMMC_RINTSTS_DCRC_E_ACT   | 0x1   | Clears Data CRC error (DCRC)
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_DCRC
 * 
 * Data CRC error (DCRC)
 */
#define ALT_SDMMC_RINTSTS_DCRC_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_DCRC
 * 
 * Clears Data CRC error (DCRC)
 */
#define ALT_SDMMC_RINTSTS_DCRC_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_DCRC register field. */
#define ALT_SDMMC_RINTSTS_DCRC_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_DCRC register field. */
#define ALT_SDMMC_RINTSTS_DCRC_MSB        7
/* The width in bits of the ALT_SDMMC_RINTSTS_DCRC register field. */
#define ALT_SDMMC_RINTSTS_DCRC_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_DCRC register field value. */
#define ALT_SDMMC_RINTSTS_DCRC_SET_MSK    0x00000080
/* The mask used to clear the ALT_SDMMC_RINTSTS_DCRC register field value. */
#define ALT_SDMMC_RINTSTS_DCRC_CLR_MSK    0xffffff7f
/* The reset value of the ALT_SDMMC_RINTSTS_DCRC register field. */
#define ALT_SDMMC_RINTSTS_DCRC_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_DCRC field value from a register. */
#define ALT_SDMMC_RINTSTS_DCRC_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_SDMMC_RINTSTS_DCRC register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_DCRC_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Response Timeout Boot Ack Received - bar
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                                    
 * :------------------------------|:------|:------------------------------------------------
 *  ALT_SDMMC_RINTSTS_BAR_E_INACT | 0x0   | Response timeout (RTO)/Boot Ack Received (BAR) 
 *  ALT_SDMMC_RINTSTS_BAR_E_ACT   | 0x1   | Clears Response timeout (RTO)/Boot Ack Received
 * :                              |       | (BAR)                                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_BAR
 * 
 * Response timeout (RTO)/Boot Ack Received (BAR)
 */
#define ALT_SDMMC_RINTSTS_BAR_E_INACT   0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_BAR
 * 
 * Clears Response timeout (RTO)/Boot Ack Received (BAR)
 */
#define ALT_SDMMC_RINTSTS_BAR_E_ACT     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_BAR register field. */
#define ALT_SDMMC_RINTSTS_BAR_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_BAR register field. */
#define ALT_SDMMC_RINTSTS_BAR_MSB        8
/* The width in bits of the ALT_SDMMC_RINTSTS_BAR register field. */
#define ALT_SDMMC_RINTSTS_BAR_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_BAR register field value. */
#define ALT_SDMMC_RINTSTS_BAR_SET_MSK    0x00000100
/* The mask used to clear the ALT_SDMMC_RINTSTS_BAR register field value. */
#define ALT_SDMMC_RINTSTS_BAR_CLR_MSK    0xfffffeff
/* The reset value of the ALT_SDMMC_RINTSTS_BAR register field. */
#define ALT_SDMMC_RINTSTS_BAR_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_BAR field value from a register. */
#define ALT_SDMMC_RINTSTS_BAR_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_SDMMC_RINTSTS_BAR register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_BAR_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Data Read Timeout Boot Data Start - bds
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                                    
 * :------------------------------|:------|:------------------------------------------------
 *  ALT_SDMMC_RINTSTS_BDS_E_INACT | 0x0   | Data read timeout (DRTO)/Boot Data Start (BDS) 
 *  ALT_SDMMC_RINTSTS_BDS_E_ACT   | 0x1   | Clears Data read timeout (DRTO)/Boot Data Start
 * :                              |       | (BDS)                                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_BDS
 * 
 * Data read timeout (DRTO)/Boot Data Start (BDS)
 */
#define ALT_SDMMC_RINTSTS_BDS_E_INACT   0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_BDS
 * 
 * Clears Data read timeout (DRTO)/Boot Data Start (BDS)
 */
#define ALT_SDMMC_RINTSTS_BDS_E_ACT     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_BDS register field. */
#define ALT_SDMMC_RINTSTS_BDS_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_BDS register field. */
#define ALT_SDMMC_RINTSTS_BDS_MSB        9
/* The width in bits of the ALT_SDMMC_RINTSTS_BDS register field. */
#define ALT_SDMMC_RINTSTS_BDS_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_BDS register field value. */
#define ALT_SDMMC_RINTSTS_BDS_SET_MSK    0x00000200
/* The mask used to clear the ALT_SDMMC_RINTSTS_BDS register field value. */
#define ALT_SDMMC_RINTSTS_BDS_CLR_MSK    0xfffffdff
/* The reset value of the ALT_SDMMC_RINTSTS_BDS register field. */
#define ALT_SDMMC_RINTSTS_BDS_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_BDS field value from a register. */
#define ALT_SDMMC_RINTSTS_BDS_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_SDMMC_RINTSTS_BDS register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_BDS_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Data Starvation Host Timeout Volt Switch_int - hto
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                                 
 * :------------------------------|:------|:---------------------------------------------
 *  ALT_SDMMC_RINTSTS_HTO_E_INACT | 0x0   | Data starvation-by-host timeout (HTO)       
 * :                              |       | /Volt_switch_int                            
 *  ALT_SDMMC_RINTSTS_HTO_E_ACT   | 0x1   | Clears Data starvation-by-host timeout (HTO)
 * :                              |       | /Volt_switch_int                            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_HTO
 * 
 * Data starvation-by-host timeout (HTO) /Volt_switch_int
 */
#define ALT_SDMMC_RINTSTS_HTO_E_INACT   0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_HTO
 * 
 * Clears Data starvation-by-host timeout (HTO) /Volt_switch_int
 */
#define ALT_SDMMC_RINTSTS_HTO_E_ACT     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_HTO register field. */
#define ALT_SDMMC_RINTSTS_HTO_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_HTO register field. */
#define ALT_SDMMC_RINTSTS_HTO_MSB        10
/* The width in bits of the ALT_SDMMC_RINTSTS_HTO register field. */
#define ALT_SDMMC_RINTSTS_HTO_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_HTO register field value. */
#define ALT_SDMMC_RINTSTS_HTO_SET_MSK    0x00000400
/* The mask used to clear the ALT_SDMMC_RINTSTS_HTO register field value. */
#define ALT_SDMMC_RINTSTS_HTO_CLR_MSK    0xfffffbff
/* The reset value of the ALT_SDMMC_RINTSTS_HTO register field. */
#define ALT_SDMMC_RINTSTS_HTO_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_HTO field value from a register. */
#define ALT_SDMMC_RINTSTS_HTO_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_SDMMC_RINTSTS_HTO register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_HTO_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : FIFO Underrun Overrun Error - frun
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description                             
 * :-------------------------------|:------|:-----------------------------------------
 *  ALT_SDMMC_RINTSTS_FRUN_E_INACT | 0x0   | FIFO underrun/overrun error (FRUN)      
 *  ALT_SDMMC_RINTSTS_FRUN_E_ACT   | 0x1   | Clear FIFO underrun/overrun error (FRUN)
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_FRUN
 * 
 * FIFO underrun/overrun error (FRUN)
 */
#define ALT_SDMMC_RINTSTS_FRUN_E_INACT  0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_FRUN
 * 
 * Clear FIFO underrun/overrun error (FRUN)
 */
#define ALT_SDMMC_RINTSTS_FRUN_E_ACT    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_FRUN register field. */
#define ALT_SDMMC_RINTSTS_FRUN_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_FRUN register field. */
#define ALT_SDMMC_RINTSTS_FRUN_MSB        11
/* The width in bits of the ALT_SDMMC_RINTSTS_FRUN register field. */
#define ALT_SDMMC_RINTSTS_FRUN_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_FRUN register field value. */
#define ALT_SDMMC_RINTSTS_FRUN_SET_MSK    0x00000800
/* The mask used to clear the ALT_SDMMC_RINTSTS_FRUN register field value. */
#define ALT_SDMMC_RINTSTS_FRUN_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_SDMMC_RINTSTS_FRUN register field. */
#define ALT_SDMMC_RINTSTS_FRUN_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_FRUN field value from a register. */
#define ALT_SDMMC_RINTSTS_FRUN_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_SDMMC_RINTSTS_FRUN register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_FRUN_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : Hardware Locked Write Error - hle
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                             
 * :------------------------------|:------|:-----------------------------------------
 *  ALT_SDMMC_RINTSTS_HLE_E_INACT | 0x0   | Hardware locked write error (HLE)       
 *  ALT_SDMMC_RINTSTS_HLE_E_ACT   | 0x1   | Clears Hardware locked write error (HLE)
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_HLE
 * 
 * Hardware locked write error (HLE)
 */
#define ALT_SDMMC_RINTSTS_HLE_E_INACT   0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_HLE
 * 
 * Clears Hardware locked write error (HLE)
 */
#define ALT_SDMMC_RINTSTS_HLE_E_ACT     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_HLE register field. */
#define ALT_SDMMC_RINTSTS_HLE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_HLE register field. */
#define ALT_SDMMC_RINTSTS_HLE_MSB        12
/* The width in bits of the ALT_SDMMC_RINTSTS_HLE register field. */
#define ALT_SDMMC_RINTSTS_HLE_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_HLE register field value. */
#define ALT_SDMMC_RINTSTS_HLE_SET_MSK    0x00001000
/* The mask used to clear the ALT_SDMMC_RINTSTS_HLE register field value. */
#define ALT_SDMMC_RINTSTS_HLE_CLR_MSK    0xffffefff
/* The reset value of the ALT_SDMMC_RINTSTS_HLE register field. */
#define ALT_SDMMC_RINTSTS_HLE_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_HLE field value from a register. */
#define ALT_SDMMC_RINTSTS_HLE_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_SDMMC_RINTSTS_HLE register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_HLE_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : Start-bit error (SBE) - sbe
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                 
 * :------------------------------|:------|:-----------------------------
 *  ALT_SDMMC_RINTSTS_SBE_E_INACT | 0x0   | Start-bit error (SBE)       
 *  ALT_SDMMC_RINTSTS_SBE_E_ACT   | 0x1   | Clears Start-bit error (SBE)
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_SBE
 * 
 * Start-bit error (SBE)
 */
#define ALT_SDMMC_RINTSTS_SBE_E_INACT   0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_SBE
 * 
 * Clears Start-bit error (SBE)
 */
#define ALT_SDMMC_RINTSTS_SBE_E_ACT     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_SBE register field. */
#define ALT_SDMMC_RINTSTS_SBE_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_SBE register field. */
#define ALT_SDMMC_RINTSTS_SBE_MSB        13
/* The width in bits of the ALT_SDMMC_RINTSTS_SBE register field. */
#define ALT_SDMMC_RINTSTS_SBE_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_SBE register field value. */
#define ALT_SDMMC_RINTSTS_SBE_SET_MSK    0x00002000
/* The mask used to clear the ALT_SDMMC_RINTSTS_SBE register field value. */
#define ALT_SDMMC_RINTSTS_SBE_CLR_MSK    0xffffdfff
/* The reset value of the ALT_SDMMC_RINTSTS_SBE register field. */
#define ALT_SDMMC_RINTSTS_SBE_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_SBE field value from a register. */
#define ALT_SDMMC_RINTSTS_SBE_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_SDMMC_RINTSTS_SBE register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_SBE_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : Auto Cmommand Done - acd
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                 
 * :------------------------------|:------|:-----------------------------
 *  ALT_SDMMC_RINTSTS_ACD_E_INACT | 0x0   | Auto command done (ACD)     
 *  ALT_SDMMC_RINTSTS_ACD_E_ACT   | 0x1   | Clear Auto command done (ACD
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_ACD
 * 
 * Auto command done (ACD)
 */
#define ALT_SDMMC_RINTSTS_ACD_E_INACT   0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_ACD
 * 
 * Clear Auto command done (ACD
 */
#define ALT_SDMMC_RINTSTS_ACD_E_ACT     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_ACD register field. */
#define ALT_SDMMC_RINTSTS_ACD_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_ACD register field. */
#define ALT_SDMMC_RINTSTS_ACD_MSB        14
/* The width in bits of the ALT_SDMMC_RINTSTS_ACD register field. */
#define ALT_SDMMC_RINTSTS_ACD_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_ACD register field value. */
#define ALT_SDMMC_RINTSTS_ACD_SET_MSK    0x00004000
/* The mask used to clear the ALT_SDMMC_RINTSTS_ACD register field value. */
#define ALT_SDMMC_RINTSTS_ACD_CLR_MSK    0xffffbfff
/* The reset value of the ALT_SDMMC_RINTSTS_ACD register field. */
#define ALT_SDMMC_RINTSTS_ACD_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_ACD field value from a register. */
#define ALT_SDMMC_RINTSTS_ACD_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_SDMMC_RINTSTS_ACD register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_ACD_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : End-bit Error - ebe
 * 
 * Writes to bits clear status bit. Value of 1 clears status bit, and value of 0
 * leaves bit intact. Bits are logged regardless of interrupt mask status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                                   
 * :------------------------------|:------|:-----------------------------------------------
 *  ALT_SDMMC_RINTSTS_EBE_E_INACT | 0x0   | End-bit error (read)/write no CRC (EBE)       
 *  ALT_SDMMC_RINTSTS_EBE_E_ACT   | 0x1   | Clears End-bit error (read)/write no CRC (EBE)
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_EBE
 * 
 * End-bit error (read)/write no CRC (EBE)
 */
#define ALT_SDMMC_RINTSTS_EBE_E_INACT   0x0
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_EBE
 * 
 * Clears End-bit error (read)/write no CRC (EBE)
 */
#define ALT_SDMMC_RINTSTS_EBE_E_ACT     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_EBE register field. */
#define ALT_SDMMC_RINTSTS_EBE_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_EBE register field. */
#define ALT_SDMMC_RINTSTS_EBE_MSB        15
/* The width in bits of the ALT_SDMMC_RINTSTS_EBE register field. */
#define ALT_SDMMC_RINTSTS_EBE_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_EBE register field value. */
#define ALT_SDMMC_RINTSTS_EBE_SET_MSK    0x00008000
/* The mask used to clear the ALT_SDMMC_RINTSTS_EBE register field value. */
#define ALT_SDMMC_RINTSTS_EBE_CLR_MSK    0xffff7fff
/* The reset value of the ALT_SDMMC_RINTSTS_EBE register field. */
#define ALT_SDMMC_RINTSTS_EBE_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_EBE field value from a register. */
#define ALT_SDMMC_RINTSTS_EBE_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_SDMMC_RINTSTS_EBE register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_EBE_SET(value) (((value) << 15) & 0x00008000)

/*
 * Field : SDIO Interrupt - sdio_interrupt
 * 
 * Interrupt from SDIO card.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                   
 * :-----------------------------------|:------|:-------------------------------
 *  ALT_SDMMC_RINTSTS_SDIO_INT_E_ACT   | 0x1   | SDIO interrupt from card bit  
 *  ALT_SDMMC_RINTSTS_SDIO_INT_E_INACT | 0x0   | No SDIO interrupt from card bi
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_SDIO_INT
 * 
 * SDIO interrupt from card bit
 */
#define ALT_SDMMC_RINTSTS_SDIO_INT_E_ACT    0x1
/*
 * Enumerated value for register field ALT_SDMMC_RINTSTS_SDIO_INT
 * 
 * No SDIO interrupt from card bi
 */
#define ALT_SDMMC_RINTSTS_SDIO_INT_E_INACT  0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RINTSTS_SDIO_INT register field. */
#define ALT_SDMMC_RINTSTS_SDIO_INT_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RINTSTS_SDIO_INT register field. */
#define ALT_SDMMC_RINTSTS_SDIO_INT_MSB        16
/* The width in bits of the ALT_SDMMC_RINTSTS_SDIO_INT register field. */
#define ALT_SDMMC_RINTSTS_SDIO_INT_WIDTH      1
/* The mask used to set the ALT_SDMMC_RINTSTS_SDIO_INT register field value. */
#define ALT_SDMMC_RINTSTS_SDIO_INT_SET_MSK    0x00010000
/* The mask used to clear the ALT_SDMMC_RINTSTS_SDIO_INT register field value. */
#define ALT_SDMMC_RINTSTS_SDIO_INT_CLR_MSK    0xfffeffff
/* The reset value of the ALT_SDMMC_RINTSTS_SDIO_INT register field. */
#define ALT_SDMMC_RINTSTS_SDIO_INT_RESET      0x0
/* Extracts the ALT_SDMMC_RINTSTS_SDIO_INT field value from a register. */
#define ALT_SDMMC_RINTSTS_SDIO_INT_GET(value) (((value) & 0x00010000) >> 16)
/* Produces a ALT_SDMMC_RINTSTS_SDIO_INT register field value suitable for setting the register. */
#define ALT_SDMMC_RINTSTS_SDIO_INT_SET(value) (((value) << 16) & 0x00010000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_RINTSTS.
 */
struct ALT_SDMMC_RINTSTS_s
{
    uint32_t  cd             :  1;  /* Card Detect */
    uint32_t  re             :  1;  /* Response Error */
    uint32_t  cmd            :  1;  /* Command Done */
    uint32_t  dto            :  1;  /* Data Transfer Over */
    uint32_t  txdr           :  1;  /* Transmit FIFO Data Request */
    uint32_t  rxdr           :  1;  /* Receive FIFO Data Request */
    uint32_t  rcrc           :  1;  /* Response CRC Error */
    uint32_t  dcrc           :  1;  /* Data CRC Error */
    uint32_t  bar            :  1;  /* Response Timeout Boot Ack Received */
    uint32_t  bds            :  1;  /* Data Read Timeout Boot Data Start */
    uint32_t  hto            :  1;  /* Data Starvation Host Timeout Volt Switch_int */
    uint32_t  frun           :  1;  /* FIFO Underrun Overrun Error */
    uint32_t  hle            :  1;  /* Hardware Locked Write Error */
    uint32_t  sbe            :  1;  /* Start-bit error (SBE) */
    uint32_t  acd            :  1;  /* Auto Cmommand Done */
    uint32_t  ebe            :  1;  /* End-bit Error */
    uint32_t  sdio_interrupt :  1;  /* SDIO Interrupt */
    uint32_t                 : 15;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_RINTSTS. */
typedef volatile struct ALT_SDMMC_RINTSTS_s  ALT_SDMMC_RINTSTS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_RINTSTS register from the beginning of the component. */
#define ALT_SDMMC_RINTSTS_OFST        0x44

/*
 * Register : Status Register - status
 * 
 * Reports various operting status conditions.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description       
 * :--------|:-------|:------|:-------------------
 *  [0]     | R      | 0x0   | FIFO Rx Watermark 
 *  [1]     | R      | 0x1   | FIFO Tx Watermark 
 *  [2]     | R      | 0x1   | FIFO Empty        
 *  [3]     | R      | 0x0   | FIFO Full         
 *  [7:4]   | R      | 0x0   | Command FSM States
 *  [8]     | R      | 0x1   | Data 3 Status     
 *  [9]     | R      | 0x0   | Data Busy         
 *  [10]    | R      | 0x0   | Data State MC Busy
 *  [16:11] | R      | 0x0   | Response Index    
 *  [29:17] | R      | 0x0   | FIFO Count        
 *  [31:30] | ???    | 0x0   | *UNDEFINED*       
 * 
 */
/*
 * Field : FIFO Rx Watermark - fifo_rx_watermark
 * 
 * FIFO reached Receive watermark level; not qualified with data transfer
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                             | Value | Description                                     
 * :-------------------------------------------------|:------|:-------------------------------------------------
 *  ALT_SDMMC_STAT_FIFO_RX_WATERMARK_E_RXWATERMARK   | 0x0   | FIFO reached watermark level; not qualified with
 * :                                                 |       | data transfer.                                  
 *  ALT_SDMMC_STAT_FIFO_RX_WATERMARK_E_NORXWATERMARK | 0x1   | FIFO not at watermark Level                     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_STAT_FIFO_RX_WATERMARK
 * 
 * FIFO reached watermark level; not qualified with data transfer.
 */
#define ALT_SDMMC_STAT_FIFO_RX_WATERMARK_E_RXWATERMARK      0x0
/*
 * Enumerated value for register field ALT_SDMMC_STAT_FIFO_RX_WATERMARK
 * 
 * FIFO not at watermark Level
 */
#define ALT_SDMMC_STAT_FIFO_RX_WATERMARK_E_NORXWATERMARK    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_STAT_FIFO_RX_WATERMARK register field. */
#define ALT_SDMMC_STAT_FIFO_RX_WATERMARK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_STAT_FIFO_RX_WATERMARK register field. */
#define ALT_SDMMC_STAT_FIFO_RX_WATERMARK_MSB        0
/* The width in bits of the ALT_SDMMC_STAT_FIFO_RX_WATERMARK register field. */
#define ALT_SDMMC_STAT_FIFO_RX_WATERMARK_WIDTH      1
/* The mask used to set the ALT_SDMMC_STAT_FIFO_RX_WATERMARK register field value. */
#define ALT_SDMMC_STAT_FIFO_RX_WATERMARK_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_STAT_FIFO_RX_WATERMARK register field value. */
#define ALT_SDMMC_STAT_FIFO_RX_WATERMARK_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_STAT_FIFO_RX_WATERMARK register field. */
#define ALT_SDMMC_STAT_FIFO_RX_WATERMARK_RESET      0x0
/* Extracts the ALT_SDMMC_STAT_FIFO_RX_WATERMARK field value from a register. */
#define ALT_SDMMC_STAT_FIFO_RX_WATERMARK_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_STAT_FIFO_RX_WATERMARK register field value suitable for setting the register. */
#define ALT_SDMMC_STAT_FIFO_RX_WATERMARK_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : FIFO Tx Watermark - fifo_tx_watermark
 * 
 * FIFO reached Transmit watermark level; not qualified with data transfer.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                             | Value | Description                               
 * :-------------------------------------------------|:------|:-------------------------------------------
 *  ALT_SDMMC_STAT_FIFO_TX_WATERMARK_E_TXWATERMARK   | 0x1   | FIFO reached transmit watermark level: not
 * :                                                 |       | qualified with data transfer.             
 *  ALT_SDMMC_STAT_FIFO_TX_WATERMARK_E_NOTXWATERMARK | 0x0   | FIFO not at transmit watermark Level      
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_STAT_FIFO_TX_WATERMARK
 * 
 * FIFO reached transmit watermark level: not qualified with data transfer.
 */
#define ALT_SDMMC_STAT_FIFO_TX_WATERMARK_E_TXWATERMARK      0x1
/*
 * Enumerated value for register field ALT_SDMMC_STAT_FIFO_TX_WATERMARK
 * 
 * FIFO not at transmit watermark Level
 */
#define ALT_SDMMC_STAT_FIFO_TX_WATERMARK_E_NOTXWATERMARK    0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_STAT_FIFO_TX_WATERMARK register field. */
#define ALT_SDMMC_STAT_FIFO_TX_WATERMARK_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_STAT_FIFO_TX_WATERMARK register field. */
#define ALT_SDMMC_STAT_FIFO_TX_WATERMARK_MSB        1
/* The width in bits of the ALT_SDMMC_STAT_FIFO_TX_WATERMARK register field. */
#define ALT_SDMMC_STAT_FIFO_TX_WATERMARK_WIDTH      1
/* The mask used to set the ALT_SDMMC_STAT_FIFO_TX_WATERMARK register field value. */
#define ALT_SDMMC_STAT_FIFO_TX_WATERMARK_SET_MSK    0x00000002
/* The mask used to clear the ALT_SDMMC_STAT_FIFO_TX_WATERMARK register field value. */
#define ALT_SDMMC_STAT_FIFO_TX_WATERMARK_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SDMMC_STAT_FIFO_TX_WATERMARK register field. */
#define ALT_SDMMC_STAT_FIFO_TX_WATERMARK_RESET      0x1
/* Extracts the ALT_SDMMC_STAT_FIFO_TX_WATERMARK field value from a register. */
#define ALT_SDMMC_STAT_FIFO_TX_WATERMARK_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SDMMC_STAT_FIFO_TX_WATERMARK register field value suitable for setting the register. */
#define ALT_SDMMC_STAT_FIFO_TX_WATERMARK_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : FIFO Empty - fifo_empty
 * 
 * FIFO is empty status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                     | Value | Description   
 * :-----------------------------------------|:------|:---------------
 *  ALT_SDMMC_STAT_FIFO_EMPTY_E_FIFOEMPTY    | 0x1   | FIFO is empty 
 *  ALT_SDMMC_STAT_FIFO_EMPTY_E_FIFONOTEMPTY | 0x0   | FIFO not empty
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_STAT_FIFO_EMPTY
 * 
 * FIFO is empty
 */
#define ALT_SDMMC_STAT_FIFO_EMPTY_E_FIFOEMPTY       0x1
/*
 * Enumerated value for register field ALT_SDMMC_STAT_FIFO_EMPTY
 * 
 * FIFO not empty
 */
#define ALT_SDMMC_STAT_FIFO_EMPTY_E_FIFONOTEMPTY    0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_STAT_FIFO_EMPTY register field. */
#define ALT_SDMMC_STAT_FIFO_EMPTY_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_STAT_FIFO_EMPTY register field. */
#define ALT_SDMMC_STAT_FIFO_EMPTY_MSB        2
/* The width in bits of the ALT_SDMMC_STAT_FIFO_EMPTY register field. */
#define ALT_SDMMC_STAT_FIFO_EMPTY_WIDTH      1
/* The mask used to set the ALT_SDMMC_STAT_FIFO_EMPTY register field value. */
#define ALT_SDMMC_STAT_FIFO_EMPTY_SET_MSK    0x00000004
/* The mask used to clear the ALT_SDMMC_STAT_FIFO_EMPTY register field value. */
#define ALT_SDMMC_STAT_FIFO_EMPTY_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SDMMC_STAT_FIFO_EMPTY register field. */
#define ALT_SDMMC_STAT_FIFO_EMPTY_RESET      0x1
/* Extracts the ALT_SDMMC_STAT_FIFO_EMPTY field value from a register. */
#define ALT_SDMMC_STAT_FIFO_EMPTY_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SDMMC_STAT_FIFO_EMPTY register field value suitable for setting the register. */
#define ALT_SDMMC_STAT_FIFO_EMPTY_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : FIFO Full - fifo_full
 * 
 * FIFO is full status.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description     
 * :---------------------------------------|:------|:-----------------
 *  ALT_SDMMC_STAT_FIFO_FULL_E_FIFOFULL    | 0x0   | FIFO is full    
 *  ALT_SDMMC_STAT_FIFO_FULL_E_FIFONOTFULL | 0x1   | FIFO is not full
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_STAT_FIFO_FULL
 * 
 * FIFO is full
 */
#define ALT_SDMMC_STAT_FIFO_FULL_E_FIFOFULL     0x0
/*
 * Enumerated value for register field ALT_SDMMC_STAT_FIFO_FULL
 * 
 * FIFO is not full
 */
#define ALT_SDMMC_STAT_FIFO_FULL_E_FIFONOTFULL  0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_STAT_FIFO_FULL register field. */
#define ALT_SDMMC_STAT_FIFO_FULL_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_STAT_FIFO_FULL register field. */
#define ALT_SDMMC_STAT_FIFO_FULL_MSB        3
/* The width in bits of the ALT_SDMMC_STAT_FIFO_FULL register field. */
#define ALT_SDMMC_STAT_FIFO_FULL_WIDTH      1
/* The mask used to set the ALT_SDMMC_STAT_FIFO_FULL register field value. */
#define ALT_SDMMC_STAT_FIFO_FULL_SET_MSK    0x00000008
/* The mask used to clear the ALT_SDMMC_STAT_FIFO_FULL register field value. */
#define ALT_SDMMC_STAT_FIFO_FULL_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SDMMC_STAT_FIFO_FULL register field. */
#define ALT_SDMMC_STAT_FIFO_FULL_RESET      0x0
/* Extracts the ALT_SDMMC_STAT_FIFO_FULL field value from a register. */
#define ALT_SDMMC_STAT_FIFO_FULL_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SDMMC_STAT_FIFO_FULL register field value suitable for setting the register. */
#define ALT_SDMMC_STAT_FIFO_FULL_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Command FSM States - command_fsm_states
 * 
 * The command FSM state.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                          | Value | Description                                
 * :----------------------------------------------|:------|:--------------------------------------------
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_IDLEANDOTHERS | 0x0   | Idle, Wait for CCS, Send CCSD, or Boot Mode
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_SENDINITSEQ   | 0x1   | Send init sequence                         
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_TXCMDSTART    | 0x2   | Tx cmd start bit                           
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_TXCMDTXBIT    | 0x3   | Tx cmd tx bit                              
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_TXCMDINDXARG  | 0x4   | Tx cmd index + arg                         
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_TXCMDCRC7     | 0x5   | Tx cmd crc7                                
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_TXCMDEND      | 0x6   | Tx cmd end bit                             
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_RXRESPSTART   | 0x7   | Rx resp start bit                          
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_RXRESPIRQ     | 0x8   | Rx resp IRQ response                       
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_RXRESPTX      | 0x9   | Rx resp tx bit                             
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_RXRESPCMDIDX  | 0xa   | Rx resp cmd idx                            
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_RXRESPDATA    | 0xb   | Rx resp data                               
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_RXRESPCRC7    | 0xc   | Rx resp crc7                               
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_RXRESPEND     | 0xd   | Rx resp end bit                            
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_CMDPATHWAIT   | 0xe   | Cmd path wait NCC                          
 *  ALT_SDMMC_STAT_CMD_FSM_STATES_E_WAITCMDTURN   | 0xf   | Wait: CMD-to-reponse turnaround            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Idle, Wait for CCS, Send CCSD, or Boot Mode
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_IDLEANDOTHERS   0x0
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Send init sequence
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_SENDINITSEQ     0x1
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Tx cmd start bit
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_TXCMDSTART      0x2
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Tx cmd tx bit
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_TXCMDTXBIT      0x3
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Tx cmd index + arg
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_TXCMDINDXARG    0x4
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Tx cmd crc7
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_TXCMDCRC7       0x5
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Tx cmd end bit
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_TXCMDEND        0x6
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Rx resp start bit
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_RXRESPSTART     0x7
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Rx resp IRQ response
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_RXRESPIRQ       0x8
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Rx resp tx bit
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_RXRESPTX        0x9
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Rx resp cmd idx
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_RXRESPCMDIDX    0xa
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Rx resp data
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_RXRESPDATA      0xb
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Rx resp crc7
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_RXRESPCRC7      0xc
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Rx resp end bit
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_RXRESPEND       0xd
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Cmd path wait NCC
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_CMDPATHWAIT     0xe
/*
 * Enumerated value for register field ALT_SDMMC_STAT_CMD_FSM_STATES
 * 
 * Wait: CMD-to-reponse turnaround
 */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_E_WAITCMDTURN     0xf

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_STAT_CMD_FSM_STATES register field. */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_STAT_CMD_FSM_STATES register field. */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_MSB        7
/* The width in bits of the ALT_SDMMC_STAT_CMD_FSM_STATES register field. */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_WIDTH      4
/* The mask used to set the ALT_SDMMC_STAT_CMD_FSM_STATES register field value. */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_SET_MSK    0x000000f0
/* The mask used to clear the ALT_SDMMC_STAT_CMD_FSM_STATES register field value. */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_CLR_MSK    0xffffff0f
/* The reset value of the ALT_SDMMC_STAT_CMD_FSM_STATES register field. */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_RESET      0x0
/* Extracts the ALT_SDMMC_STAT_CMD_FSM_STATES field value from a register. */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_GET(value) (((value) & 0x000000f0) >> 4)
/* Produces a ALT_SDMMC_STAT_CMD_FSM_STATES register field value suitable for setting the register. */
#define ALT_SDMMC_STAT_CMD_FSM_STATES_SET(value) (((value) << 4) & 0x000000f0)

/*
 * Field : Data 3 Status - data_3_status
 * 
 * Raw selected card_data[3]; checks whether card is present. The default can be
 * cardpresent or not present depend on cdata_in.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                        | Value | Description     
 * :--------------------------------------------|:------|:-----------------
 *  ALT_SDMMC_STAT_DATA_3_STAT_E_CARDPRESENT    | 0x1   | Card Present    
 *  ALT_SDMMC_STAT_DATA_3_STAT_E_CARDNOTPRESENT | 0x0   | Card Not Present
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_STAT_DATA_3_STAT
 * 
 * Card Present
 */
#define ALT_SDMMC_STAT_DATA_3_STAT_E_CARDPRESENT    0x1
/*
 * Enumerated value for register field ALT_SDMMC_STAT_DATA_3_STAT
 * 
 * Card Not Present
 */
#define ALT_SDMMC_STAT_DATA_3_STAT_E_CARDNOTPRESENT 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_STAT_DATA_3_STAT register field. */
#define ALT_SDMMC_STAT_DATA_3_STAT_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_STAT_DATA_3_STAT register field. */
#define ALT_SDMMC_STAT_DATA_3_STAT_MSB        8
/* The width in bits of the ALT_SDMMC_STAT_DATA_3_STAT register field. */
#define ALT_SDMMC_STAT_DATA_3_STAT_WIDTH      1
/* The mask used to set the ALT_SDMMC_STAT_DATA_3_STAT register field value. */
#define ALT_SDMMC_STAT_DATA_3_STAT_SET_MSK    0x00000100
/* The mask used to clear the ALT_SDMMC_STAT_DATA_3_STAT register field value. */
#define ALT_SDMMC_STAT_DATA_3_STAT_CLR_MSK    0xfffffeff
/* The reset value of the ALT_SDMMC_STAT_DATA_3_STAT register field. */
#define ALT_SDMMC_STAT_DATA_3_STAT_RESET      0x1
/* Extracts the ALT_SDMMC_STAT_DATA_3_STAT field value from a register. */
#define ALT_SDMMC_STAT_DATA_3_STAT_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_SDMMC_STAT_DATA_3_STAT register field value suitable for setting the register. */
#define ALT_SDMMC_STAT_DATA_3_STAT_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Data Busy - data_busy
 * 
 * Inverted version of raw selected card_data[0]. The default can be cardpresent or
 * not present depend on cdata_in.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description       
 * :---------------------------------------|:------|:-------------------
 *  ALT_SDMMC_STAT_DATA_BUSY_E_CARDBUSY    | 0x1   | card data busy    
 *  ALT_SDMMC_STAT_DATA_BUSY_E_CARDNOTBUSY | 0x0   | card data not busy
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_STAT_DATA_BUSY
 * 
 * card data busy
 */
#define ALT_SDMMC_STAT_DATA_BUSY_E_CARDBUSY     0x1
/*
 * Enumerated value for register field ALT_SDMMC_STAT_DATA_BUSY
 * 
 * card data not busy
 */
#define ALT_SDMMC_STAT_DATA_BUSY_E_CARDNOTBUSY  0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_STAT_DATA_BUSY register field. */
#define ALT_SDMMC_STAT_DATA_BUSY_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_STAT_DATA_BUSY register field. */
#define ALT_SDMMC_STAT_DATA_BUSY_MSB        9
/* The width in bits of the ALT_SDMMC_STAT_DATA_BUSY register field. */
#define ALT_SDMMC_STAT_DATA_BUSY_WIDTH      1
/* The mask used to set the ALT_SDMMC_STAT_DATA_BUSY register field value. */
#define ALT_SDMMC_STAT_DATA_BUSY_SET_MSK    0x00000200
/* The mask used to clear the ALT_SDMMC_STAT_DATA_BUSY register field value. */
#define ALT_SDMMC_STAT_DATA_BUSY_CLR_MSK    0xfffffdff
/* The reset value of the ALT_SDMMC_STAT_DATA_BUSY register field. */
#define ALT_SDMMC_STAT_DATA_BUSY_RESET      0x0
/* Extracts the ALT_SDMMC_STAT_DATA_BUSY field value from a register. */
#define ALT_SDMMC_STAT_DATA_BUSY_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_SDMMC_STAT_DATA_BUSY register field value suitable for setting the register. */
#define ALT_SDMMC_STAT_DATA_BUSY_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Data State MC Busy - data_state_mc_busy
 * 
 * Data transmit or receive state-machine is busy.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                | Value | Description           
 * :----------------------------------------------------|:------|:-----------------------
 *  ALT_SDMMC_STAT_DATA_STATE_MC_BUSY_E_DATASTATEBSY    | 0x1   | Data State MC busy    
 *  ALT_SDMMC_STAT_DATA_STATE_MC_BUSY_E_DATASTATENOTBSY | 0x0   | Data State MC not busy
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_STAT_DATA_STATE_MC_BUSY
 * 
 * Data State MC busy
 */
#define ALT_SDMMC_STAT_DATA_STATE_MC_BUSY_E_DATASTATEBSY    0x1
/*
 * Enumerated value for register field ALT_SDMMC_STAT_DATA_STATE_MC_BUSY
 * 
 * Data State MC not busy
 */
#define ALT_SDMMC_STAT_DATA_STATE_MC_BUSY_E_DATASTATENOTBSY 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_STAT_DATA_STATE_MC_BUSY register field. */
#define ALT_SDMMC_STAT_DATA_STATE_MC_BUSY_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_STAT_DATA_STATE_MC_BUSY register field. */
#define ALT_SDMMC_STAT_DATA_STATE_MC_BUSY_MSB        10
/* The width in bits of the ALT_SDMMC_STAT_DATA_STATE_MC_BUSY register field. */
#define ALT_SDMMC_STAT_DATA_STATE_MC_BUSY_WIDTH      1
/* The mask used to set the ALT_SDMMC_STAT_DATA_STATE_MC_BUSY register field value. */
#define ALT_SDMMC_STAT_DATA_STATE_MC_BUSY_SET_MSK    0x00000400
/* The mask used to clear the ALT_SDMMC_STAT_DATA_STATE_MC_BUSY register field value. */
#define ALT_SDMMC_STAT_DATA_STATE_MC_BUSY_CLR_MSK    0xfffffbff
/* The reset value of the ALT_SDMMC_STAT_DATA_STATE_MC_BUSY register field. */
#define ALT_SDMMC_STAT_DATA_STATE_MC_BUSY_RESET      0x0
/* Extracts the ALT_SDMMC_STAT_DATA_STATE_MC_BUSY field value from a register. */
#define ALT_SDMMC_STAT_DATA_STATE_MC_BUSY_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_SDMMC_STAT_DATA_STATE_MC_BUSY register field value suitable for setting the register. */
#define ALT_SDMMC_STAT_DATA_STATE_MC_BUSY_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Response Index - response_index
 * 
 * Index of previous response, including any auto-stop sent by core
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_STAT_RESPONSE_INDEX register field. */
#define ALT_SDMMC_STAT_RESPONSE_INDEX_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_STAT_RESPONSE_INDEX register field. */
#define ALT_SDMMC_STAT_RESPONSE_INDEX_MSB        16
/* The width in bits of the ALT_SDMMC_STAT_RESPONSE_INDEX register field. */
#define ALT_SDMMC_STAT_RESPONSE_INDEX_WIDTH      6
/* The mask used to set the ALT_SDMMC_STAT_RESPONSE_INDEX register field value. */
#define ALT_SDMMC_STAT_RESPONSE_INDEX_SET_MSK    0x0001f800
/* The mask used to clear the ALT_SDMMC_STAT_RESPONSE_INDEX register field value. */
#define ALT_SDMMC_STAT_RESPONSE_INDEX_CLR_MSK    0xfffe07ff
/* The reset value of the ALT_SDMMC_STAT_RESPONSE_INDEX register field. */
#define ALT_SDMMC_STAT_RESPONSE_INDEX_RESET      0x0
/* Extracts the ALT_SDMMC_STAT_RESPONSE_INDEX field value from a register. */
#define ALT_SDMMC_STAT_RESPONSE_INDEX_GET(value) (((value) & 0x0001f800) >> 11)
/* Produces a ALT_SDMMC_STAT_RESPONSE_INDEX register field value suitable for setting the register. */
#define ALT_SDMMC_STAT_RESPONSE_INDEX_SET(value) (((value) << 11) & 0x0001f800)

/*
 * Field : FIFO Count - fifo_count
 * 
 * FIFO count - Number of filled locations in FIFO
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_STAT_FIFO_COUNT register field. */
#define ALT_SDMMC_STAT_FIFO_COUNT_LSB        17
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_STAT_FIFO_COUNT register field. */
#define ALT_SDMMC_STAT_FIFO_COUNT_MSB        29
/* The width in bits of the ALT_SDMMC_STAT_FIFO_COUNT register field. */
#define ALT_SDMMC_STAT_FIFO_COUNT_WIDTH      13
/* The mask used to set the ALT_SDMMC_STAT_FIFO_COUNT register field value. */
#define ALT_SDMMC_STAT_FIFO_COUNT_SET_MSK    0x3ffe0000
/* The mask used to clear the ALT_SDMMC_STAT_FIFO_COUNT register field value. */
#define ALT_SDMMC_STAT_FIFO_COUNT_CLR_MSK    0xc001ffff
/* The reset value of the ALT_SDMMC_STAT_FIFO_COUNT register field. */
#define ALT_SDMMC_STAT_FIFO_COUNT_RESET      0x0
/* Extracts the ALT_SDMMC_STAT_FIFO_COUNT field value from a register. */
#define ALT_SDMMC_STAT_FIFO_COUNT_GET(value) (((value) & 0x3ffe0000) >> 17)
/* Produces a ALT_SDMMC_STAT_FIFO_COUNT register field value suitable for setting the register. */
#define ALT_SDMMC_STAT_FIFO_COUNT_SET(value) (((value) << 17) & 0x3ffe0000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_STAT.
 */
struct ALT_SDMMC_STAT_s
{
    const uint32_t  fifo_rx_watermark  :  1;  /* FIFO Rx Watermark */
    const uint32_t  fifo_tx_watermark  :  1;  /* FIFO Tx Watermark */
    const uint32_t  fifo_empty         :  1;  /* FIFO Empty */
    const uint32_t  fifo_full          :  1;  /* FIFO Full */
    const uint32_t  command_fsm_states :  4;  /* Command FSM States */
    const uint32_t  data_3_status      :  1;  /* Data 3 Status */
    const uint32_t  data_busy          :  1;  /* Data Busy */
    const uint32_t  data_state_mc_busy :  1;  /* Data State MC Busy */
    const uint32_t  response_index     :  6;  /* Response Index */
    const uint32_t  fifo_count         : 13;  /* FIFO Count */
    uint32_t                           :  2;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_STAT. */
typedef volatile struct ALT_SDMMC_STAT_s  ALT_SDMMC_STAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_STAT register from the beginning of the component. */
#define ALT_SDMMC_STAT_OFST        0x48

/*
 * Register : FIFO Threshold Watermark Register - fifoth
 * 
 * DMA and FIFO Control Fields.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                  
 * :--------|:-------|:------|:------------------------------
 *  [11:0]  | RW     | 0x0   | Tx WMark                     
 *  [15:12] | ???    | 0x0   | *UNDEFINED*                  
 *  [27:16] | RW     | 0x3ff | Rx WMark                     
 *  [30:28] | RW     | 0x0   | DMA Multiple Transaction Size
 *  [31]    | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : Tx WMark - tx_wmark
 * 
 * FIFO threshold watermark level when transmitting data to card. When FIFO data
 * count is less than or equal to this number, DMA/FIFO request is raised. If
 * Interrupt is enabled, then interrupt occurs. During end of packet, request or
 * interrupt is generated, regardless of threshold programming. In non-DMA mode,
 * when transmit FIFO threshold (TXDR) interrupt is enabled, then interrupt is
 * generated instead of DMA request. During end of packet, on last interrupt, host
 * is responsible for filling FIFO with only required remaining bytes (not before
 * FIFO is full or after CIU completes data transfers, because FIFO may not be
 * empty). In DMA mode, at end of packet, if last transfer is less than burst size,
 * DMA controller does single cycles until required bytes are transferred. 12 bits
 * - 1 bit less than FIFO-count of status register, which is 13 bits.
 * 
 * Limitation: TX_WMark >= 1;
 * 
 * Recommended: FIFO_DEPTH/2 = 512; (means less than or equal to 512)
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_FIFOTH_TX_WMARK register field. */
#define ALT_SDMMC_FIFOTH_TX_WMARK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_FIFOTH_TX_WMARK register field. */
#define ALT_SDMMC_FIFOTH_TX_WMARK_MSB        11
/* The width in bits of the ALT_SDMMC_FIFOTH_TX_WMARK register field. */
#define ALT_SDMMC_FIFOTH_TX_WMARK_WIDTH      12
/* The mask used to set the ALT_SDMMC_FIFOTH_TX_WMARK register field value. */
#define ALT_SDMMC_FIFOTH_TX_WMARK_SET_MSK    0x00000fff
/* The mask used to clear the ALT_SDMMC_FIFOTH_TX_WMARK register field value. */
#define ALT_SDMMC_FIFOTH_TX_WMARK_CLR_MSK    0xfffff000
/* The reset value of the ALT_SDMMC_FIFOTH_TX_WMARK register field. */
#define ALT_SDMMC_FIFOTH_TX_WMARK_RESET      0x0
/* Extracts the ALT_SDMMC_FIFOTH_TX_WMARK field value from a register. */
#define ALT_SDMMC_FIFOTH_TX_WMARK_GET(value) (((value) & 0x00000fff) >> 0)
/* Produces a ALT_SDMMC_FIFOTH_TX_WMARK register field value suitable for setting the register. */
#define ALT_SDMMC_FIFOTH_TX_WMARK_SET(value) (((value) << 0) & 0x00000fff)

/*
 * Field : Rx WMark - rx_wmark
 * 
 * FIFO threshold watermark level when receiving data to card. When FIFO data count
 * reaches greater than this number, DMA/FIFO request is raised. During end of
 * packet, request is generated regardless of threshold programming in order to
 * complete any remaining data. In non-DMA mode, when receiver FIFO threshold
 * (RXDR) interrupt is enabled, then interrupt is generated instead of DMA request.
 * During end of packet, interrupt is not generated if threshold programming is
 * larger than any remaining data. It is responsibility of host to read remaining
 * bytes on seeing Data Transfer Done interrupt. In DMA mode, at end of packet,
 * even if remaining bytes are less than threshold, DMA request does single
 * transfers to flush out any remaining bytes before Data Transfer Done interrupt
 * is set. 12 bits - 1 bit less than FIFO-count of status register, which is 13
 * bits.
 * 
 * Limitation: RX_WMark <= 1022
 * 
 * Recommended: 511; means greater than (FIFO_DEPTH/2) - 1)
 * 
 * NOTE: In DMA mode during CCS time-out, the DMA does not generate the request at
 * the end of packet, even if remaining bytes are less than threshold. In this
 * case, there will be some data left in the FIFO. It is the responsibility of the
 * application to reset the FIFO after the CCS timeout.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_FIFOTH_RX_WMARK register field. */
#define ALT_SDMMC_FIFOTH_RX_WMARK_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_FIFOTH_RX_WMARK register field. */
#define ALT_SDMMC_FIFOTH_RX_WMARK_MSB        27
/* The width in bits of the ALT_SDMMC_FIFOTH_RX_WMARK register field. */
#define ALT_SDMMC_FIFOTH_RX_WMARK_WIDTH      12
/* The mask used to set the ALT_SDMMC_FIFOTH_RX_WMARK register field value. */
#define ALT_SDMMC_FIFOTH_RX_WMARK_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_SDMMC_FIFOTH_RX_WMARK register field value. */
#define ALT_SDMMC_FIFOTH_RX_WMARK_CLR_MSK    0xf000ffff
/* The reset value of the ALT_SDMMC_FIFOTH_RX_WMARK register field. */
#define ALT_SDMMC_FIFOTH_RX_WMARK_RESET      0x3ff
/* Extracts the ALT_SDMMC_FIFOTH_RX_WMARK field value from a register. */
#define ALT_SDMMC_FIFOTH_RX_WMARK_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_SDMMC_FIFOTH_RX_WMARK register field value suitable for setting the register. */
#define ALT_SDMMC_FIFOTH_RX_WMARK_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : DMA Multiple Transaction Size - dw_dma_multiple_transaction_size
 * 
 * Burst size of multiple transaction; should be programmed same as DMA controller
 * multiple-transaction-size SRC/DEST_MSIZE.
 * 
 * The units for transfers is 32 bits. A single transfer would be signalled based
 * on this value. Value should be sub-multiple of 512. Allowed combinations for
 * MSize and TX_WMark.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                       | Value | Description                
 * :-----------------------------------------------------------|:------|:----------------------------
 *  ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_E_TXMSIZE1   | 0x0   | Msize 1 and TX_WMARK 1-1023
 *  ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_E_TXMSIZE4   | 0x1   | Msize 4 and TX_WMARK 256   
 *  ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_E_TXMSIZEK8  | 0x2   | Msize 8 and TX_WMARK 128   
 *  ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_E_TXMSIZEK16 | 0x3   | Msize 16 and TX_WMARK 64   
 *  ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_E_RXMSIZEK1  | 0x5   | Msize 1 and RX_WMARK 512   
 *  ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_E_RXMSIZEK4  | 0x6   | Msize 4 and RX_WMARK 128   
 *  ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_E_RXMSIZE8   | 0x7   | Msize 8 and RX_WMARK 64    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE
 * 
 * Msize 1 and TX_WMARK 1-1023
 */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_E_TXMSIZE1    0x0
/*
 * Enumerated value for register field ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE
 * 
 * Msize 4 and TX_WMARK 256
 */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_E_TXMSIZE4    0x1
/*
 * Enumerated value for register field ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE
 * 
 * Msize 8 and TX_WMARK 128
 */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_E_TXMSIZEK8   0x2
/*
 * Enumerated value for register field ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE
 * 
 * Msize 16 and TX_WMARK 64
 */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_E_TXMSIZEK16  0x3
/*
 * Enumerated value for register field ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE
 * 
 * Msize 1 and RX_WMARK 512
 */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_E_RXMSIZEK1   0x5
/*
 * Enumerated value for register field ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE
 * 
 * Msize 4 and RX_WMARK 128
 */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_E_RXMSIZEK4   0x6
/*
 * Enumerated value for register field ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE
 * 
 * Msize 8 and RX_WMARK 64
 */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_E_RXMSIZE8    0x7

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE register field. */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_LSB        28
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE register field. */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_MSB        30
/* The width in bits of the ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE register field. */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_WIDTH      3
/* The mask used to set the ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE register field value. */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_SET_MSK    0x70000000
/* The mask used to clear the ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE register field value. */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_CLR_MSK    0x8fffffff
/* The reset value of the ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE register field. */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_RESET      0x0
/* Extracts the ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE field value from a register. */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_GET(value) (((value) & 0x70000000) >> 28)
/* Produces a ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE register field value suitable for setting the register. */
#define ALT_SDMMC_FIFOTH_DW_DMA_MULT_TRANSACTION_SIZE_SET(value) (((value) << 28) & 0x70000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_FIFOTH.
 */
struct ALT_SDMMC_FIFOTH_s
{
    uint32_t  tx_wmark                         : 12;  /* Tx WMark */
    uint32_t                                   :  4;  /* *UNDEFINED* */
    uint32_t  rx_wmark                         : 12;  /* Rx WMark */
    uint32_t  dw_dma_multiple_transaction_size :  3;  /* DMA Multiple Transaction Size */
    uint32_t                                   :  1;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_FIFOTH. */
typedef volatile struct ALT_SDMMC_FIFOTH_s  ALT_SDMMC_FIFOTH_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_FIFOTH register from the beginning of the component. */
#define ALT_SDMMC_FIFOTH_OFST        0x4c

/*
 * Register : Card Detect Register - cdetect
 * 
 * Determines if card is present.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [0]    | R      | 0x1   | Card Detect
 *  [31:1] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Card Detect - card_detect_n
 * 
 * Value on sdmmc_cd_i input port.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                          | Value | Description      
 * :----------------------------------------------|:------|:------------------
 *  ALT_SDMMC_CDETECT_CARD_DETECT_N_E_NOTDETECTED | 0x1   | Card not Detected
 *  ALT_SDMMC_CDETECT_CARD_DETECT_N_E_DETECTED    | 0x0   | Card Detected    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CDETECT_CARD_DETECT_N
 * 
 * Card not Detected
 */
#define ALT_SDMMC_CDETECT_CARD_DETECT_N_E_NOTDETECTED   0x1
/*
 * Enumerated value for register field ALT_SDMMC_CDETECT_CARD_DETECT_N
 * 
 * Card Detected
 */
#define ALT_SDMMC_CDETECT_CARD_DETECT_N_E_DETECTED      0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CDETECT_CARD_DETECT_N register field. */
#define ALT_SDMMC_CDETECT_CARD_DETECT_N_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CDETECT_CARD_DETECT_N register field. */
#define ALT_SDMMC_CDETECT_CARD_DETECT_N_MSB        0
/* The width in bits of the ALT_SDMMC_CDETECT_CARD_DETECT_N register field. */
#define ALT_SDMMC_CDETECT_CARD_DETECT_N_WIDTH      1
/* The mask used to set the ALT_SDMMC_CDETECT_CARD_DETECT_N register field value. */
#define ALT_SDMMC_CDETECT_CARD_DETECT_N_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_CDETECT_CARD_DETECT_N register field value. */
#define ALT_SDMMC_CDETECT_CARD_DETECT_N_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_CDETECT_CARD_DETECT_N register field. */
#define ALT_SDMMC_CDETECT_CARD_DETECT_N_RESET      0x1
/* Extracts the ALT_SDMMC_CDETECT_CARD_DETECT_N field value from a register. */
#define ALT_SDMMC_CDETECT_CARD_DETECT_N_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_CDETECT_CARD_DETECT_N register field value suitable for setting the register. */
#define ALT_SDMMC_CDETECT_CARD_DETECT_N_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_CDETECT.
 */
struct ALT_SDMMC_CDETECT_s
{
    const uint32_t  card_detect_n :  1;  /* Card Detect */
    uint32_t                      : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_CDETECT. */
typedef volatile struct ALT_SDMMC_CDETECT_s  ALT_SDMMC_CDETECT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_CDETECT register from the beginning of the component. */
#define ALT_SDMMC_CDETECT_OFST        0x50

/*
 * Register : Write Protect Register - wrtprt
 * 
 * See Field Description.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description  
 * :-------|:-------|:------|:--------------
 *  [0]    | R      | 0x1   | Write Protect
 *  [31:1] | ???    | 0x0   | *UNDEFINED*  
 * 
 */
/*
 * Field : Write Protect - write_protect
 * 
 * Value on sdmmc_wp_i input port.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description           
 * :-----------------------------------|:------|:-----------------------
 *  ALT_SDMMC_WRTPRT_WR_PROTECT_E_END  | 0x1   | Write Protect Enabled 
 *  ALT_SDMMC_WRTPRT_WR_PROTECT_E_DISD | 0x0   | Write Protect Disabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_WRTPRT_WR_PROTECT
 * 
 * Write Protect Enabled
 */
#define ALT_SDMMC_WRTPRT_WR_PROTECT_E_END   0x1
/*
 * Enumerated value for register field ALT_SDMMC_WRTPRT_WR_PROTECT
 * 
 * Write Protect Disabled
 */
#define ALT_SDMMC_WRTPRT_WR_PROTECT_E_DISD  0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_WRTPRT_WR_PROTECT register field. */
#define ALT_SDMMC_WRTPRT_WR_PROTECT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_WRTPRT_WR_PROTECT register field. */
#define ALT_SDMMC_WRTPRT_WR_PROTECT_MSB        0
/* The width in bits of the ALT_SDMMC_WRTPRT_WR_PROTECT register field. */
#define ALT_SDMMC_WRTPRT_WR_PROTECT_WIDTH      1
/* The mask used to set the ALT_SDMMC_WRTPRT_WR_PROTECT register field value. */
#define ALT_SDMMC_WRTPRT_WR_PROTECT_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_WRTPRT_WR_PROTECT register field value. */
#define ALT_SDMMC_WRTPRT_WR_PROTECT_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_WRTPRT_WR_PROTECT register field. */
#define ALT_SDMMC_WRTPRT_WR_PROTECT_RESET      0x1
/* Extracts the ALT_SDMMC_WRTPRT_WR_PROTECT field value from a register. */
#define ALT_SDMMC_WRTPRT_WR_PROTECT_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_WRTPRT_WR_PROTECT register field value suitable for setting the register. */
#define ALT_SDMMC_WRTPRT_WR_PROTECT_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_WRTPRT.
 */
struct ALT_SDMMC_WRTPRT_s
{
    const uint32_t  write_protect :  1;  /* Write Protect */
    uint32_t                      : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_WRTPRT. */
typedef volatile struct ALT_SDMMC_WRTPRT_s  ALT_SDMMC_WRTPRT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_WRTPRT register from the beginning of the component. */
#define ALT_SDMMC_WRTPRT_OFST        0x54

/*
 * Register : Transferred CIU Card Byte Count Register - tcbcnt
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description          
 * :-------|:-------|:------|:----------------------
 *  [31:0] | R      | 0x0   | Trans Card Byte Count
 * 
 */
/*
 * Field : Trans Card Byte Count - trans_card_byte_count
 * 
 * Number of bytes transferred by CIU unit to card.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT register field. */
#define ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT register field. */
#define ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT_MSB        31
/* The width in bits of the ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT register field. */
#define ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT_WIDTH      32
/* The mask used to set the ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT register field value. */
#define ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT register field value. */
#define ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT_CLR_MSK    0x00000000
/* The reset value of the ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT register field. */
#define ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT_RESET      0x0
/* Extracts the ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT field value from a register. */
#define ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT register field value suitable for setting the register. */
#define ALT_SDMMC_TCBCNT_TRANS_CARD_BYTE_COUNT_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_TCBCNT.
 */
struct ALT_SDMMC_TCBCNT_s
{
    const uint32_t  trans_card_byte_count : 32;  /* Trans Card Byte Count */
};

/* The typedef declaration for register ALT_SDMMC_TCBCNT. */
typedef volatile struct ALT_SDMMC_TCBCNT_s  ALT_SDMMC_TCBCNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_TCBCNT register from the beginning of the component. */
#define ALT_SDMMC_TCBCNT_OFST        0x5c

/*
 * Register : Transferred Host to BIU-FIFO Byte Count Register - tbbcnt
 * 
 * Tracks number of bytes transferred between Host and FIFO.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description          
 * :-------|:-------|:------|:----------------------
 *  [31:0] | R      | 0x0   | Trans FIFO Byte Count
 * 
 */
/*
 * Field : Trans FIFO Byte Count - trans_fifo_byte_count
 * 
 * Number of bytes transferred between Host/DMA memory and BIU FIFO. In 32-bit AMBA
 * data-bus-width modes, register should be accessed in full to avoid read-
 * coherency problems. Both TCBCNT and TBBCNT share same coherency register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT register field. */
#define ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT register field. */
#define ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT_MSB        31
/* The width in bits of the ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT register field. */
#define ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT_WIDTH      32
/* The mask used to set the ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT register field value. */
#define ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT register field value. */
#define ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT_CLR_MSK    0x00000000
/* The reset value of the ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT register field. */
#define ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT_RESET      0x0
/* Extracts the ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT field value from a register. */
#define ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT register field value suitable for setting the register. */
#define ALT_SDMMC_TBBCNT_TRANS_FIFO_BYTE_COUNT_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_TBBCNT.
 */
struct ALT_SDMMC_TBBCNT_s
{
    const uint32_t  trans_fifo_byte_count : 32;  /* Trans FIFO Byte Count */
};

/* The typedef declaration for register ALT_SDMMC_TBBCNT. */
typedef volatile struct ALT_SDMMC_TBBCNT_s  ALT_SDMMC_TBBCNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_TBBCNT register from the beginning of the component. */
#define ALT_SDMMC_TBBCNT_OFST        0x60

/*
 * Register : Debounce Count Register - debnce
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset    | Description   
 * :--------|:-------|:---------|:---------------
 *  [23:0]  | RW     | 0xffffff | Debounce Count
 *  [31:24] | ???    | 0x0      | *UNDEFINED*   
 * 
 */
/*
 * Field : Debounce Count - debounce_count
 * 
 * Number of host clocks l4_mp_clk used by debounce filter logic; typical debounce
 * time is 5-25 ms.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT register field. */
#define ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT register field. */
#define ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT_MSB        23
/* The width in bits of the ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT register field. */
#define ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT_WIDTH      24
/* The mask used to set the ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT register field value. */
#define ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT_SET_MSK    0x00ffffff
/* The mask used to clear the ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT register field value. */
#define ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT_CLR_MSK    0xff000000
/* The reset value of the ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT register field. */
#define ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT_RESET      0xffffff
/* Extracts the ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT field value from a register. */
#define ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT_GET(value) (((value) & 0x00ffffff) >> 0)
/* Produces a ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT register field value suitable for setting the register. */
#define ALT_SDMMC_DEBNCE_DEBOUNCE_COUNT_SET(value) (((value) << 0) & 0x00ffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_DEBNCE.
 */
struct ALT_SDMMC_DEBNCE_s
{
    uint32_t  debounce_count : 24;  /* Debounce Count */
    uint32_t                 :  8;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_DEBNCE. */
typedef volatile struct ALT_SDMMC_DEBNCE_s  ALT_SDMMC_DEBNCE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_DEBNCE register from the beginning of the component. */
#define ALT_SDMMC_DEBNCE_OFST        0x64

/*
 * Register : User ID Register - usrid
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset     | Description
 * :-------|:-------|:----------|:------------
 *  [31:0] | RW     | 0x7967797 | User ID    
 * 
 */
/*
 * Field : User ID - usr_id
 * 
 * User identification field; Value is 0x7967797.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_USRID_USR_ID register field. */
#define ALT_SDMMC_USRID_USR_ID_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_USRID_USR_ID register field. */
#define ALT_SDMMC_USRID_USR_ID_MSB        31
/* The width in bits of the ALT_SDMMC_USRID_USR_ID register field. */
#define ALT_SDMMC_USRID_USR_ID_WIDTH      32
/* The mask used to set the ALT_SDMMC_USRID_USR_ID register field value. */
#define ALT_SDMMC_USRID_USR_ID_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDMMC_USRID_USR_ID register field value. */
#define ALT_SDMMC_USRID_USR_ID_CLR_MSK    0x00000000
/* The reset value of the ALT_SDMMC_USRID_USR_ID register field. */
#define ALT_SDMMC_USRID_USR_ID_RESET      0x7967797
/* Extracts the ALT_SDMMC_USRID_USR_ID field value from a register. */
#define ALT_SDMMC_USRID_USR_ID_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDMMC_USRID_USR_ID register field value suitable for setting the register. */
#define ALT_SDMMC_USRID_USR_ID_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_USRID.
 */
struct ALT_SDMMC_USRID_s
{
    uint32_t  usr_id : 32;  /* User ID */
};

/* The typedef declaration for register ALT_SDMMC_USRID. */
typedef volatile struct ALT_SDMMC_USRID_s  ALT_SDMMC_USRID_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_USRID register from the beginning of the component. */
#define ALT_SDMMC_USRID_OFST        0x68

/*
 * Register : Version ID Register - verid
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset      | Description
 * :-------|:-------|:-----------|:------------
 *  [31:0] | R      | 0x5342240a | Version ID 
 * 
 */
/*
 * Field : Version ID - ver_id
 * 
 * Synopsys version id. Current value is 32'h5342240a
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_VERID_VER_ID register field. */
#define ALT_SDMMC_VERID_VER_ID_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_VERID_VER_ID register field. */
#define ALT_SDMMC_VERID_VER_ID_MSB        31
/* The width in bits of the ALT_SDMMC_VERID_VER_ID register field. */
#define ALT_SDMMC_VERID_VER_ID_WIDTH      32
/* The mask used to set the ALT_SDMMC_VERID_VER_ID register field value. */
#define ALT_SDMMC_VERID_VER_ID_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDMMC_VERID_VER_ID register field value. */
#define ALT_SDMMC_VERID_VER_ID_CLR_MSK    0x00000000
/* The reset value of the ALT_SDMMC_VERID_VER_ID register field. */
#define ALT_SDMMC_VERID_VER_ID_RESET      0x5342240a
/* Extracts the ALT_SDMMC_VERID_VER_ID field value from a register. */
#define ALT_SDMMC_VERID_VER_ID_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDMMC_VERID_VER_ID register field value suitable for setting the register. */
#define ALT_SDMMC_VERID_VER_ID_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_VERID.
 */
struct ALT_SDMMC_VERID_s
{
    const uint32_t  ver_id : 32;  /* Version ID */
};

/* The typedef declaration for register ALT_SDMMC_VERID. */
typedef volatile struct ALT_SDMMC_VERID_s  ALT_SDMMC_VERID_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_VERID register from the beginning of the component. */
#define ALT_SDMMC_VERID_OFST        0x6c

/*
 * Register : Hardware Configuration Register - hcon
 * 
 * Hardware configurations registers. Register can be used to develop
 * configuration-independent software drivers.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description             
 * :--------|:-------|:------|:-------------------------
 *  [0]     | R      | 0x1   | Card Type               
 *  [5:1]   | R      | 0x0   | Number of Cards         
 *  [6]     | R      | 0x0   | Slave Bus Type          
 *  [9:7]   | R      | 0x1   | Slave Bus Data Width    
 *  [15:10] | R      | 0xc   | Slave Bus Address Width 
 *  [17:16] | R      | 0x0   | DMA Interface Type      
 *  [20:18] | R      | 0x1   | Generic DMA Data Width  
 *  [21]    | R      | 0x0   | FIFO RAM Location       
 *  [22]    | R      | 0x1   | Implement Hold Register 
 *  [23]    | R      | 0x1   | Clock False Path        
 *  [25:24] | R      | 0x0   | Number of Clock Dividers
 *  [26]    | R      | 0x0   | Area Optimized          
 *  [31:27] | ???    | 0x0   | *UNDEFINED*             
 * 
 */
/*
 * Field : Card Type - ct
 * 
 * Supported card types
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description     
 * :--------------------------|:------|:-----------------
 *  ALT_SDMMC_HCON_CT_E_SDMMC | 0x1   | Card Type SD/MMC
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_HCON_CT
 * 
 * Card Type SD/MMC
 */
#define ALT_SDMMC_HCON_CT_E_SDMMC   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_HCON_CT register field. */
#define ALT_SDMMC_HCON_CT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_HCON_CT register field. */
#define ALT_SDMMC_HCON_CT_MSB        0
/* The width in bits of the ALT_SDMMC_HCON_CT register field. */
#define ALT_SDMMC_HCON_CT_WIDTH      1
/* The mask used to set the ALT_SDMMC_HCON_CT register field value. */
#define ALT_SDMMC_HCON_CT_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_HCON_CT register field value. */
#define ALT_SDMMC_HCON_CT_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_HCON_CT register field. */
#define ALT_SDMMC_HCON_CT_RESET      0x1
/* Extracts the ALT_SDMMC_HCON_CT field value from a register. */
#define ALT_SDMMC_HCON_CT_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_HCON_CT register field value suitable for setting the register. */
#define ALT_SDMMC_HCON_CT_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Number of Cards - nc
 * 
 * Maximum number of cards less one
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description
 * :----------------------------|:------|:------------
 *  ALT_SDMMC_HCON_NC_E_NUMCARD | 0x0   | 1 Card     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_HCON_NC
 * 
 * 1 Card
 */
#define ALT_SDMMC_HCON_NC_E_NUMCARD 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_HCON_NC register field. */
#define ALT_SDMMC_HCON_NC_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_HCON_NC register field. */
#define ALT_SDMMC_HCON_NC_MSB        5
/* The width in bits of the ALT_SDMMC_HCON_NC register field. */
#define ALT_SDMMC_HCON_NC_WIDTH      5
/* The mask used to set the ALT_SDMMC_HCON_NC register field value. */
#define ALT_SDMMC_HCON_NC_SET_MSK    0x0000003e
/* The mask used to clear the ALT_SDMMC_HCON_NC register field value. */
#define ALT_SDMMC_HCON_NC_CLR_MSK    0xffffffc1
/* The reset value of the ALT_SDMMC_HCON_NC register field. */
#define ALT_SDMMC_HCON_NC_RESET      0x0
/* Extracts the ALT_SDMMC_HCON_NC field value from a register. */
#define ALT_SDMMC_HCON_NC_GET(value) (((value) & 0x0000003e) >> 1)
/* Produces a ALT_SDMMC_HCON_NC register field value suitable for setting the register. */
#define ALT_SDMMC_HCON_NC_SET(value) (((value) << 1) & 0x0000003e)

/*
 * Field : Slave Bus Type - hbus
 * 
 * Slave bus type.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description
 * :--------------------------|:------|:------------
 *  ALT_SDMMC_HCON_HBUS_E_APB | 0x0   | APB Bus    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_HCON_HBUS
 * 
 * APB Bus
 */
#define ALT_SDMMC_HCON_HBUS_E_APB   0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_HCON_HBUS register field. */
#define ALT_SDMMC_HCON_HBUS_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_HCON_HBUS register field. */
#define ALT_SDMMC_HCON_HBUS_MSB        6
/* The width in bits of the ALT_SDMMC_HCON_HBUS register field. */
#define ALT_SDMMC_HCON_HBUS_WIDTH      1
/* The mask used to set the ALT_SDMMC_HCON_HBUS register field value. */
#define ALT_SDMMC_HCON_HBUS_SET_MSK    0x00000040
/* The mask used to clear the ALT_SDMMC_HCON_HBUS register field value. */
#define ALT_SDMMC_HCON_HBUS_CLR_MSK    0xffffffbf
/* The reset value of the ALT_SDMMC_HCON_HBUS register field. */
#define ALT_SDMMC_HCON_HBUS_RESET      0x0
/* Extracts the ALT_SDMMC_HCON_HBUS field value from a register. */
#define ALT_SDMMC_HCON_HBUS_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_SDMMC_HCON_HBUS register field value suitable for setting the register. */
#define ALT_SDMMC_HCON_HBUS_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Slave Bus Data Width - hdatawidth
 * 
 * Slave bus data width
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                    | Value | Description  
 * :----------------------------------------|:------|:--------------
 *  ALT_SDMMC_HCON_HDATAWIDTH_E_WIDTH32BITS | 0x1   | Width 32 Bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_HCON_HDATAWIDTH
 * 
 * Width 32 Bits
 */
#define ALT_SDMMC_HCON_HDATAWIDTH_E_WIDTH32BITS 0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_HCON_HDATAWIDTH register field. */
#define ALT_SDMMC_HCON_HDATAWIDTH_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_HCON_HDATAWIDTH register field. */
#define ALT_SDMMC_HCON_HDATAWIDTH_MSB        9
/* The width in bits of the ALT_SDMMC_HCON_HDATAWIDTH register field. */
#define ALT_SDMMC_HCON_HDATAWIDTH_WIDTH      3
/* The mask used to set the ALT_SDMMC_HCON_HDATAWIDTH register field value. */
#define ALT_SDMMC_HCON_HDATAWIDTH_SET_MSK    0x00000380
/* The mask used to clear the ALT_SDMMC_HCON_HDATAWIDTH register field value. */
#define ALT_SDMMC_HCON_HDATAWIDTH_CLR_MSK    0xfffffc7f
/* The reset value of the ALT_SDMMC_HCON_HDATAWIDTH register field. */
#define ALT_SDMMC_HCON_HDATAWIDTH_RESET      0x1
/* Extracts the ALT_SDMMC_HCON_HDATAWIDTH field value from a register. */
#define ALT_SDMMC_HCON_HDATAWIDTH_GET(value) (((value) & 0x00000380) >> 7)
/* Produces a ALT_SDMMC_HCON_HDATAWIDTH register field value suitable for setting the register. */
#define ALT_SDMMC_HCON_HDATAWIDTH_SET(value) (((value) << 7) & 0x00000380)

/*
 * Field : Slave Bus Address Width - haddrwidth
 * 
 * Slave bus address width less one
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                    | Value | Description  
 * :----------------------------------------|:------|:--------------
 *  ALT_SDMMC_HCON_HADDRWIDTH_E_WIDTH13BITS | 0xc   | Width 13 Bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_HCON_HADDRWIDTH
 * 
 * Width 13 Bits
 */
#define ALT_SDMMC_HCON_HADDRWIDTH_E_WIDTH13BITS 0xc

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_HCON_HADDRWIDTH register field. */
#define ALT_SDMMC_HCON_HADDRWIDTH_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_HCON_HADDRWIDTH register field. */
#define ALT_SDMMC_HCON_HADDRWIDTH_MSB        15
/* The width in bits of the ALT_SDMMC_HCON_HADDRWIDTH register field. */
#define ALT_SDMMC_HCON_HADDRWIDTH_WIDTH      6
/* The mask used to set the ALT_SDMMC_HCON_HADDRWIDTH register field value. */
#define ALT_SDMMC_HCON_HADDRWIDTH_SET_MSK    0x0000fc00
/* The mask used to clear the ALT_SDMMC_HCON_HADDRWIDTH register field value. */
#define ALT_SDMMC_HCON_HADDRWIDTH_CLR_MSK    0xffff03ff
/* The reset value of the ALT_SDMMC_HCON_HADDRWIDTH register field. */
#define ALT_SDMMC_HCON_HADDRWIDTH_RESET      0xc
/* Extracts the ALT_SDMMC_HCON_HADDRWIDTH field value from a register. */
#define ALT_SDMMC_HCON_HADDRWIDTH_GET(value) (((value) & 0x0000fc00) >> 10)
/* Produces a ALT_SDMMC_HCON_HADDRWIDTH register field value suitable for setting the register. */
#define ALT_SDMMC_HCON_HADDRWIDTH_SET(value) (((value) << 10) & 0x0000fc00)

/*
 * Field : DMA Interface Type - dmaintf
 * 
 * DMA interface type
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                                     
 * :------------------------------|:------|:-------------------------------------------------
 *  ALT_SDMMC_HCON_DMAINTF_E_NONE | 0x0   | No External DMA Controller Interface (SD/MMC has
 * :                              |       | its own internal DMA Controller                 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_HCON_DMAINTF
 * 
 * No External DMA Controller Interface (SD/MMC has its own internal DMA Controller
 */
#define ALT_SDMMC_HCON_DMAINTF_E_NONE   0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_HCON_DMAINTF register field. */
#define ALT_SDMMC_HCON_DMAINTF_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_HCON_DMAINTF register field. */
#define ALT_SDMMC_HCON_DMAINTF_MSB        17
/* The width in bits of the ALT_SDMMC_HCON_DMAINTF register field. */
#define ALT_SDMMC_HCON_DMAINTF_WIDTH      2
/* The mask used to set the ALT_SDMMC_HCON_DMAINTF register field value. */
#define ALT_SDMMC_HCON_DMAINTF_SET_MSK    0x00030000
/* The mask used to clear the ALT_SDMMC_HCON_DMAINTF register field value. */
#define ALT_SDMMC_HCON_DMAINTF_CLR_MSK    0xfffcffff
/* The reset value of the ALT_SDMMC_HCON_DMAINTF register field. */
#define ALT_SDMMC_HCON_DMAINTF_RESET      0x0
/* Extracts the ALT_SDMMC_HCON_DMAINTF field value from a register. */
#define ALT_SDMMC_HCON_DMAINTF_GET(value) (((value) & 0x00030000) >> 16)
/* Produces a ALT_SDMMC_HCON_DMAINTF register field value suitable for setting the register. */
#define ALT_SDMMC_HCON_DMAINTF_SET(value) (((value) << 16) & 0x00030000)

/*
 * Field : Generic DMA Data Width - dmadatawidth
 * 
 * Encodes bit width of external DMA controller interface. Doesn't apply to the
 * SD/MMC because it has no external DMA controller interface.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description 
 * :------------------------------------------|:------|:-------------
 *  ALT_SDMMC_HCON_DMADATAWIDTH_E_WIDTH32BITS | 0x1   | 32-bits wide
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_HCON_DMADATAWIDTH
 * 
 * 32-bits wide
 */
#define ALT_SDMMC_HCON_DMADATAWIDTH_E_WIDTH32BITS   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_HCON_DMADATAWIDTH register field. */
#define ALT_SDMMC_HCON_DMADATAWIDTH_LSB        18
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_HCON_DMADATAWIDTH register field. */
#define ALT_SDMMC_HCON_DMADATAWIDTH_MSB        20
/* The width in bits of the ALT_SDMMC_HCON_DMADATAWIDTH register field. */
#define ALT_SDMMC_HCON_DMADATAWIDTH_WIDTH      3
/* The mask used to set the ALT_SDMMC_HCON_DMADATAWIDTH register field value. */
#define ALT_SDMMC_HCON_DMADATAWIDTH_SET_MSK    0x001c0000
/* The mask used to clear the ALT_SDMMC_HCON_DMADATAWIDTH register field value. */
#define ALT_SDMMC_HCON_DMADATAWIDTH_CLR_MSK    0xffe3ffff
/* The reset value of the ALT_SDMMC_HCON_DMADATAWIDTH register field. */
#define ALT_SDMMC_HCON_DMADATAWIDTH_RESET      0x1
/* Extracts the ALT_SDMMC_HCON_DMADATAWIDTH field value from a register. */
#define ALT_SDMMC_HCON_DMADATAWIDTH_GET(value) (((value) & 0x001c0000) >> 18)
/* Produces a ALT_SDMMC_HCON_DMADATAWIDTH register field value suitable for setting the register. */
#define ALT_SDMMC_HCON_DMADATAWIDTH_SET(value) (((value) << 18) & 0x001c0000)

/*
 * Field : FIFO RAM Location - rios
 * 
 * FIFO RAM location
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description             
 * :------------------------------|:------|:-------------------------
 *  ALT_SDMMC_HCON_RIOS_E_OUTSIDE | 0x0   | FIFO RAM Outside IP Core
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_HCON_RIOS
 * 
 * FIFO RAM Outside IP Core
 */
#define ALT_SDMMC_HCON_RIOS_E_OUTSIDE   0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_HCON_RIOS register field. */
#define ALT_SDMMC_HCON_RIOS_LSB        21
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_HCON_RIOS register field. */
#define ALT_SDMMC_HCON_RIOS_MSB        21
/* The width in bits of the ALT_SDMMC_HCON_RIOS register field. */
#define ALT_SDMMC_HCON_RIOS_WIDTH      1
/* The mask used to set the ALT_SDMMC_HCON_RIOS register field value. */
#define ALT_SDMMC_HCON_RIOS_SET_MSK    0x00200000
/* The mask used to clear the ALT_SDMMC_HCON_RIOS register field value. */
#define ALT_SDMMC_HCON_RIOS_CLR_MSK    0xffdfffff
/* The reset value of the ALT_SDMMC_HCON_RIOS register field. */
#define ALT_SDMMC_HCON_RIOS_RESET      0x0
/* Extracts the ALT_SDMMC_HCON_RIOS field value from a register. */
#define ALT_SDMMC_HCON_RIOS_GET(value) (((value) & 0x00200000) >> 21)
/* Produces a ALT_SDMMC_HCON_RIOS register field value suitable for setting the register. */
#define ALT_SDMMC_HCON_RIOS_SET(value) (((value) << 21) & 0x00200000)

/*
 * Field : Implement Hold Register - ihr
 * 
 * Implement hold register
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description             
 * :---------------------------------|:------|:-------------------------
 *  ALT_SDMMC_HCON_IHR_E_IMPLEMENTED | 0x1   | Implements Hold Register
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_HCON_IHR
 * 
 * Implements Hold Register
 */
#define ALT_SDMMC_HCON_IHR_E_IMPLEMENTED    0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_HCON_IHR register field. */
#define ALT_SDMMC_HCON_IHR_LSB        22
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_HCON_IHR register field. */
#define ALT_SDMMC_HCON_IHR_MSB        22
/* The width in bits of the ALT_SDMMC_HCON_IHR register field. */
#define ALT_SDMMC_HCON_IHR_WIDTH      1
/* The mask used to set the ALT_SDMMC_HCON_IHR register field value. */
#define ALT_SDMMC_HCON_IHR_SET_MSK    0x00400000
/* The mask used to clear the ALT_SDMMC_HCON_IHR register field value. */
#define ALT_SDMMC_HCON_IHR_CLR_MSK    0xffbfffff
/* The reset value of the ALT_SDMMC_HCON_IHR register field. */
#define ALT_SDMMC_HCON_IHR_RESET      0x1
/* Extracts the ALT_SDMMC_HCON_IHR field value from a register. */
#define ALT_SDMMC_HCON_IHR_GET(value) (((value) & 0x00400000) >> 22)
/* Produces a ALT_SDMMC_HCON_IHR register field value suitable for setting the register. */
#define ALT_SDMMC_HCON_IHR_SET(value) (((value) << 22) & 0x00400000)

/*
 * Field : Clock False Path - scfp
 * 
 * Clock False Path
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description         
 * :--------------------------|:------|:---------------------
 *  ALT_SDMMC_HCON_SCFP_E_SET | 0x1   | Clock False Path Set
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_HCON_SCFP
 * 
 * Clock False Path Set
 */
#define ALT_SDMMC_HCON_SCFP_E_SET   0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_HCON_SCFP register field. */
#define ALT_SDMMC_HCON_SCFP_LSB        23
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_HCON_SCFP register field. */
#define ALT_SDMMC_HCON_SCFP_MSB        23
/* The width in bits of the ALT_SDMMC_HCON_SCFP register field. */
#define ALT_SDMMC_HCON_SCFP_WIDTH      1
/* The mask used to set the ALT_SDMMC_HCON_SCFP register field value. */
#define ALT_SDMMC_HCON_SCFP_SET_MSK    0x00800000
/* The mask used to clear the ALT_SDMMC_HCON_SCFP register field value. */
#define ALT_SDMMC_HCON_SCFP_CLR_MSK    0xff7fffff
/* The reset value of the ALT_SDMMC_HCON_SCFP register field. */
#define ALT_SDMMC_HCON_SCFP_RESET      0x1
/* Extracts the ALT_SDMMC_HCON_SCFP field value from a register. */
#define ALT_SDMMC_HCON_SCFP_GET(value) (((value) & 0x00800000) >> 23)
/* Produces a ALT_SDMMC_HCON_SCFP register field value suitable for setting the register. */
#define ALT_SDMMC_HCON_SCFP_SET(value) (((value) << 23) & 0x00800000)

/*
 * Field : Number of Clock Dividers - ncd
 * 
 * Number of clock dividers less one
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description      
 * :----------------------------|:------|:------------------
 *  ALT_SDMMC_HCON_NCD_E_ONEDIV | 0x0   | One Clock Divider
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_HCON_NCD
 * 
 * One Clock Divider
 */
#define ALT_SDMMC_HCON_NCD_E_ONEDIV 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_HCON_NCD register field. */
#define ALT_SDMMC_HCON_NCD_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_HCON_NCD register field. */
#define ALT_SDMMC_HCON_NCD_MSB        25
/* The width in bits of the ALT_SDMMC_HCON_NCD register field. */
#define ALT_SDMMC_HCON_NCD_WIDTH      2
/* The mask used to set the ALT_SDMMC_HCON_NCD register field value. */
#define ALT_SDMMC_HCON_NCD_SET_MSK    0x03000000
/* The mask used to clear the ALT_SDMMC_HCON_NCD register field value. */
#define ALT_SDMMC_HCON_NCD_CLR_MSK    0xfcffffff
/* The reset value of the ALT_SDMMC_HCON_NCD register field. */
#define ALT_SDMMC_HCON_NCD_RESET      0x0
/* Extracts the ALT_SDMMC_HCON_NCD field value from a register. */
#define ALT_SDMMC_HCON_NCD_GET(value) (((value) & 0x03000000) >> 24)
/* Produces a ALT_SDMMC_HCON_NCD register field value suitable for setting the register. */
#define ALT_SDMMC_HCON_NCD_SET(value) (((value) << 24) & 0x03000000)

/*
 * Field : Area Optimized - aro
 * 
 * Area optimized
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description           
 * :-----------------------------------|:------|:-----------------------
 *  ALT_SDMMC_HCON_ARO_E_NOTOPTFORAREA | 0x0   | Not Optimized For Area
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_HCON_ARO
 * 
 * Not Optimized For Area
 */
#define ALT_SDMMC_HCON_ARO_E_NOTOPTFORAREA  0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_HCON_ARO register field. */
#define ALT_SDMMC_HCON_ARO_LSB        26
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_HCON_ARO register field. */
#define ALT_SDMMC_HCON_ARO_MSB        26
/* The width in bits of the ALT_SDMMC_HCON_ARO register field. */
#define ALT_SDMMC_HCON_ARO_WIDTH      1
/* The mask used to set the ALT_SDMMC_HCON_ARO register field value. */
#define ALT_SDMMC_HCON_ARO_SET_MSK    0x04000000
/* The mask used to clear the ALT_SDMMC_HCON_ARO register field value. */
#define ALT_SDMMC_HCON_ARO_CLR_MSK    0xfbffffff
/* The reset value of the ALT_SDMMC_HCON_ARO register field. */
#define ALT_SDMMC_HCON_ARO_RESET      0x0
/* Extracts the ALT_SDMMC_HCON_ARO field value from a register. */
#define ALT_SDMMC_HCON_ARO_GET(value) (((value) & 0x04000000) >> 26)
/* Produces a ALT_SDMMC_HCON_ARO register field value suitable for setting the register. */
#define ALT_SDMMC_HCON_ARO_SET(value) (((value) << 26) & 0x04000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_HCON.
 */
struct ALT_SDMMC_HCON_s
{
    const uint32_t  ct           :  1;  /* Card Type */
    const uint32_t  nc           :  5;  /* Number of Cards */
    const uint32_t  hbus         :  1;  /* Slave Bus Type */
    const uint32_t  hdatawidth   :  3;  /* Slave Bus Data Width */
    const uint32_t  haddrwidth   :  6;  /* Slave Bus Address Width */
    const uint32_t  dmaintf      :  2;  /* DMA Interface Type */
    const uint32_t  dmadatawidth :  3;  /* Generic DMA Data Width */
    const uint32_t  rios         :  1;  /* FIFO RAM Location */
    const uint32_t  ihr          :  1;  /* Implement Hold Register */
    const uint32_t  scfp         :  1;  /* Clock False Path */
    const uint32_t  ncd          :  2;  /* Number of Clock Dividers */
    const uint32_t  aro          :  1;  /* Area Optimized */
    uint32_t                     :  5;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_HCON. */
typedef volatile struct ALT_SDMMC_HCON_s  ALT_SDMMC_HCON_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_HCON register from the beginning of the component. */
#define ALT_SDMMC_HCON_OFST        0x70

/*
 * Register : UHS-1 Register - uhs_reg
 * 
 * UHS-1 Register
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description      
 * :--------|:-------|:------|:------------------
 *  [0]     | RW     | 0x0   | High Voltage Mode
 *  [15:1]  | ???    | 0x0   | *UNDEFINED*      
 *  [16]    | RW     | 0x0   | DDR Mode         
 *  [31:17] | ???    | 0x0   | *UNDEFINED*      
 * 
 */
/*
 * Field : High Voltage Mode - volt_reg
 * 
 * Determines the voltage fed to the buffers by an external voltage regulator.
 * These bits function as the output of the host controller and are fed to an
 * external voltage regulator. The voltage regulator must switch the voltage of the
 * buffers of a particular card to either 3.3V or 1.8V, depending on the value
 * programmed in the register.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                   
 * :------------------------------------|:------|:-------------------------------
 *  ALT_SDMMC_UHS_REG_VOLT_REG_E_BUF33V | 0x0   | Buffers supplied with 3.3V Vdd
 *  ALT_SDMMC_UHS_REG_VOLT_REG_E_BUF18V | 0x1   | Buffers supplied with 1.8V Vdd
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_UHS_REG_VOLT_REG
 * 
 * Buffers supplied with 3.3V Vdd
 */
#define ALT_SDMMC_UHS_REG_VOLT_REG_E_BUF33V 0x0
/*
 * Enumerated value for register field ALT_SDMMC_UHS_REG_VOLT_REG
 * 
 * Buffers supplied with 1.8V Vdd
 */
#define ALT_SDMMC_UHS_REG_VOLT_REG_E_BUF18V 0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_UHS_REG_VOLT_REG register field. */
#define ALT_SDMMC_UHS_REG_VOLT_REG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_UHS_REG_VOLT_REG register field. */
#define ALT_SDMMC_UHS_REG_VOLT_REG_MSB        0
/* The width in bits of the ALT_SDMMC_UHS_REG_VOLT_REG register field. */
#define ALT_SDMMC_UHS_REG_VOLT_REG_WIDTH      1
/* The mask used to set the ALT_SDMMC_UHS_REG_VOLT_REG register field value. */
#define ALT_SDMMC_UHS_REG_VOLT_REG_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_UHS_REG_VOLT_REG register field value. */
#define ALT_SDMMC_UHS_REG_VOLT_REG_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_UHS_REG_VOLT_REG register field. */
#define ALT_SDMMC_UHS_REG_VOLT_REG_RESET      0x0
/* Extracts the ALT_SDMMC_UHS_REG_VOLT_REG field value from a register. */
#define ALT_SDMMC_UHS_REG_VOLT_REG_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_UHS_REG_VOLT_REG register field value suitable for setting the register. */
#define ALT_SDMMC_UHS_REG_VOLT_REG_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : DDR Mode - ddr_reg
 * 
 * Determines the voltage fed to the buffers by an external voltage regulator.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description 
 * :-----------------------------------|:------|:-------------
 *  ALT_SDMMC_UHS_REG_DDR_REG_E_NONDDR | 0x0   | Non-DDR mode
 *  ALT_SDMMC_UHS_REG_DDR_REG_E_DDR    | 0x1   | DDR mode    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_UHS_REG_DDR_REG
 * 
 * Non-DDR mode
 */
#define ALT_SDMMC_UHS_REG_DDR_REG_E_NONDDR  0x0
/*
 * Enumerated value for register field ALT_SDMMC_UHS_REG_DDR_REG
 * 
 * DDR mode
 */
#define ALT_SDMMC_UHS_REG_DDR_REG_E_DDR     0x1

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_UHS_REG_DDR_REG register field. */
#define ALT_SDMMC_UHS_REG_DDR_REG_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_UHS_REG_DDR_REG register field. */
#define ALT_SDMMC_UHS_REG_DDR_REG_MSB        16
/* The width in bits of the ALT_SDMMC_UHS_REG_DDR_REG register field. */
#define ALT_SDMMC_UHS_REG_DDR_REG_WIDTH      1
/* The mask used to set the ALT_SDMMC_UHS_REG_DDR_REG register field value. */
#define ALT_SDMMC_UHS_REG_DDR_REG_SET_MSK    0x00010000
/* The mask used to clear the ALT_SDMMC_UHS_REG_DDR_REG register field value. */
#define ALT_SDMMC_UHS_REG_DDR_REG_CLR_MSK    0xfffeffff
/* The reset value of the ALT_SDMMC_UHS_REG_DDR_REG register field. */
#define ALT_SDMMC_UHS_REG_DDR_REG_RESET      0x0
/* Extracts the ALT_SDMMC_UHS_REG_DDR_REG field value from a register. */
#define ALT_SDMMC_UHS_REG_DDR_REG_GET(value) (((value) & 0x00010000) >> 16)
/* Produces a ALT_SDMMC_UHS_REG_DDR_REG register field value suitable for setting the register. */
#define ALT_SDMMC_UHS_REG_DDR_REG_SET(value) (((value) << 16) & 0x00010000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_UHS_REG.
 */
struct ALT_SDMMC_UHS_REG_s
{
    uint32_t  volt_reg :  1;  /* High Voltage Mode */
    uint32_t           : 15;  /* *UNDEFINED* */
    uint32_t  ddr_reg  :  1;  /* DDR Mode */
    uint32_t           : 15;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_UHS_REG. */
typedef volatile struct ALT_SDMMC_UHS_REG_s  ALT_SDMMC_UHS_REG_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_UHS_REG register from the beginning of the component. */
#define ALT_SDMMC_UHS_REG_OFST        0x74

/*
 * Register : Hardware Reset Register - rst_n
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [0]    | RW     | 0x1   | Card Reset 
 *  [31:1] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Card Reset - card_reset
 * 
 * This bit causes the cards to enter pre-idle state, which requires it to be re-
 * initialized.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description    
 * :------------------------------------|:------|:----------------
 *  ALT_SDMMC_RST_N_CARD_RST_E_ASSERT   | 0x1   | Active Mode    
 *  ALT_SDMMC_RST_N_CARD_RST_E_DEASSERT | 0x0   | Not Active Mode
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_RST_N_CARD_RST
 * 
 * Active Mode
 */
#define ALT_SDMMC_RST_N_CARD_RST_E_ASSERT   0x1
/*
 * Enumerated value for register field ALT_SDMMC_RST_N_CARD_RST
 * 
 * Not Active Mode
 */
#define ALT_SDMMC_RST_N_CARD_RST_E_DEASSERT 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_RST_N_CARD_RST register field. */
#define ALT_SDMMC_RST_N_CARD_RST_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_RST_N_CARD_RST register field. */
#define ALT_SDMMC_RST_N_CARD_RST_MSB        0
/* The width in bits of the ALT_SDMMC_RST_N_CARD_RST register field. */
#define ALT_SDMMC_RST_N_CARD_RST_WIDTH      1
/* The mask used to set the ALT_SDMMC_RST_N_CARD_RST register field value. */
#define ALT_SDMMC_RST_N_CARD_RST_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_RST_N_CARD_RST register field value. */
#define ALT_SDMMC_RST_N_CARD_RST_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_RST_N_CARD_RST register field. */
#define ALT_SDMMC_RST_N_CARD_RST_RESET      0x1
/* Extracts the ALT_SDMMC_RST_N_CARD_RST field value from a register. */
#define ALT_SDMMC_RST_N_CARD_RST_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_RST_N_CARD_RST register field value suitable for setting the register. */
#define ALT_SDMMC_RST_N_CARD_RST_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_RST_N.
 */
struct ALT_SDMMC_RST_N_s
{
    uint32_t  card_reset :  1;  /* Card Reset */
    uint32_t             : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_RST_N. */
typedef volatile struct ALT_SDMMC_RST_N_s  ALT_SDMMC_RST_N_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_RST_N register from the beginning of the component. */
#define ALT_SDMMC_RST_N_OFST        0x78

/*
 * Register : Bus Mode Register - bmod
 * 
 * Details different bus operating modes.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description              
 * :--------|:-------|:------|:--------------------------
 *  [0]     | RW     | 0x0   | Software Reset           
 *  [1]     | RW     | 0x0   | Fixed Burst              
 *  [6:2]   | RW     | 0x0   | Descriptor Skip Length   
 *  [7]     | RW     | 0x0   | IDMAC Enable             
 *  [10:8]  | R      | 0x0   | Programmable Burst Length
 *  [31:11] | ???    | 0x0   | *UNDEFINED*              
 * 
 */
/*
 * Field : Software Reset - swr
 * 
 * This bit resets all internal registers of the DMA Controller. It is
 * automatically cleared after 1 clock cycle.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                  
 * :------------------------------|:------|:------------------------------
 *  ALT_SDMMC_BMOD_SWR_E_SFTRST   | 0x1   | Resets DMA Internal Registers
 *  ALT_SDMMC_BMOD_SWR_E_NOSFTRST | 0x0   | No reset - default           
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_BMOD_SWR
 * 
 * Resets DMA Internal Registers
 */
#define ALT_SDMMC_BMOD_SWR_E_SFTRST     0x1
/*
 * Enumerated value for register field ALT_SDMMC_BMOD_SWR
 * 
 * No reset - default
 */
#define ALT_SDMMC_BMOD_SWR_E_NOSFTRST   0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_BMOD_SWR register field. */
#define ALT_SDMMC_BMOD_SWR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_BMOD_SWR register field. */
#define ALT_SDMMC_BMOD_SWR_MSB        0
/* The width in bits of the ALT_SDMMC_BMOD_SWR register field. */
#define ALT_SDMMC_BMOD_SWR_WIDTH      1
/* The mask used to set the ALT_SDMMC_BMOD_SWR register field value. */
#define ALT_SDMMC_BMOD_SWR_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_BMOD_SWR register field value. */
#define ALT_SDMMC_BMOD_SWR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_BMOD_SWR register field. */
#define ALT_SDMMC_BMOD_SWR_RESET      0x0
/* Extracts the ALT_SDMMC_BMOD_SWR field value from a register. */
#define ALT_SDMMC_BMOD_SWR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_BMOD_SWR register field value suitable for setting the register. */
#define ALT_SDMMC_BMOD_SWR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Fixed Burst - fb
 * 
 * Controls whether the AHB Master interface performs fixed burst transfers or not.
 * Will use only SINGLE, INCR4, INCR8 or INCR16 during start of normal burst
 * transfers.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description              
 * :--------------------------------|:------|:--------------------------
 *  ALT_SDMMC_BMOD_FB_E_FIXEDBRST   | 0x1   | AHB Master Fixed Burst   
 *  ALT_SDMMC_BMOD_FB_E_NOFIXEDBRST | 0x0   | Non Fixed Burst - default
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_BMOD_FB
 * 
 * AHB Master Fixed Burst
 */
#define ALT_SDMMC_BMOD_FB_E_FIXEDBRST   0x1
/*
 * Enumerated value for register field ALT_SDMMC_BMOD_FB
 * 
 * Non Fixed Burst - default
 */
#define ALT_SDMMC_BMOD_FB_E_NOFIXEDBRST 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_BMOD_FB register field. */
#define ALT_SDMMC_BMOD_FB_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_BMOD_FB register field. */
#define ALT_SDMMC_BMOD_FB_MSB        1
/* The width in bits of the ALT_SDMMC_BMOD_FB register field. */
#define ALT_SDMMC_BMOD_FB_WIDTH      1
/* The mask used to set the ALT_SDMMC_BMOD_FB register field value. */
#define ALT_SDMMC_BMOD_FB_SET_MSK    0x00000002
/* The mask used to clear the ALT_SDMMC_BMOD_FB register field value. */
#define ALT_SDMMC_BMOD_FB_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SDMMC_BMOD_FB register field. */
#define ALT_SDMMC_BMOD_FB_RESET      0x0
/* Extracts the ALT_SDMMC_BMOD_FB field value from a register. */
#define ALT_SDMMC_BMOD_FB_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SDMMC_BMOD_FB register field value suitable for setting the register. */
#define ALT_SDMMC_BMOD_FB_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Descriptor Skip Length - dsl
 * 
 * Specifies the number of HWord/Word/Dword (depending on 16/32/64-bit bus) to skip
 * between two unchained descriptors.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_BMOD_DSL register field. */
#define ALT_SDMMC_BMOD_DSL_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_BMOD_DSL register field. */
#define ALT_SDMMC_BMOD_DSL_MSB        6
/* The width in bits of the ALT_SDMMC_BMOD_DSL register field. */
#define ALT_SDMMC_BMOD_DSL_WIDTH      5
/* The mask used to set the ALT_SDMMC_BMOD_DSL register field value. */
#define ALT_SDMMC_BMOD_DSL_SET_MSK    0x0000007c
/* The mask used to clear the ALT_SDMMC_BMOD_DSL register field value. */
#define ALT_SDMMC_BMOD_DSL_CLR_MSK    0xffffff83
/* The reset value of the ALT_SDMMC_BMOD_DSL register field. */
#define ALT_SDMMC_BMOD_DSL_RESET      0x0
/* Extracts the ALT_SDMMC_BMOD_DSL field value from a register. */
#define ALT_SDMMC_BMOD_DSL_GET(value) (((value) & 0x0000007c) >> 2)
/* Produces a ALT_SDMMC_BMOD_DSL register field value suitable for setting the register. */
#define ALT_SDMMC_BMOD_DSL_SET(value) (((value) << 2) & 0x0000007c)

/*
 * Field : IDMAC Enable - de
 * 
 * Enables and Disables Internal DMA.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                     | Value | Description  
 * :-------------------------|:------|:--------------
 *  ALT_SDMMC_BMOD_DE_E_END  | 0x1   | IDMAC Enable 
 *  ALT_SDMMC_BMOD_DE_E_DISD | 0x0   | IDMAC Disable
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_BMOD_DE
 * 
 * IDMAC Enable
 */
#define ALT_SDMMC_BMOD_DE_E_END     0x1
/*
 * Enumerated value for register field ALT_SDMMC_BMOD_DE
 * 
 * IDMAC Disable
 */
#define ALT_SDMMC_BMOD_DE_E_DISD    0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_BMOD_DE register field. */
#define ALT_SDMMC_BMOD_DE_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_BMOD_DE register field. */
#define ALT_SDMMC_BMOD_DE_MSB        7
/* The width in bits of the ALT_SDMMC_BMOD_DE register field. */
#define ALT_SDMMC_BMOD_DE_WIDTH      1
/* The mask used to set the ALT_SDMMC_BMOD_DE register field value. */
#define ALT_SDMMC_BMOD_DE_SET_MSK    0x00000080
/* The mask used to clear the ALT_SDMMC_BMOD_DE register field value. */
#define ALT_SDMMC_BMOD_DE_CLR_MSK    0xffffff7f
/* The reset value of the ALT_SDMMC_BMOD_DE register field. */
#define ALT_SDMMC_BMOD_DE_RESET      0x0
/* Extracts the ALT_SDMMC_BMOD_DE field value from a register. */
#define ALT_SDMMC_BMOD_DE_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_SDMMC_BMOD_DE register field value suitable for setting the register. */
#define ALT_SDMMC_BMOD_DE_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Programmable Burst Length - pbl
 * 
 * These bits indicate the maximum number of beats to be performed in one IDMAC
 * transaction. The IDMAC will always attempt to burst as specified in PBL each
 * time it starts a Burst transfer on the host bus. This value is the mirror of
 * MSIZE of FIFOTH register. In order to change this value, write the required
 * value to FIFOTH register. This is an encode value as follows.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description 
 * :------------------------------|:------|:-------------
 *  ALT_SDMMC_BMOD_PBL_E_TRANS1   | 0x0   | Transfer 1  
 *  ALT_SDMMC_BMOD_PBL_E_TRANS4   | 0x1   | Transfer 4  
 *  ALT_SDMMC_BMOD_PBL_E_TRANS8   | 0x2   | Transfer 8  
 *  ALT_SDMMC_BMOD_PBL_E_TRANS16  | 0x3   | Transfer 16 
 *  ALT_SDMMC_BMOD_PBL_E_TRANS32  | 0x4   | Transfer 32 
 *  ALT_SDMMC_BMOD_PBL_E_TRANS64  | 0x5   | Transfer 64 
 *  ALT_SDMMC_BMOD_PBL_E_TRANS128 | 0x6   | Transfer 128
 *  ALT_SDMMC_BMOD_PBL_E_TRANS256 | 0x7   | Transfer 256
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_BMOD_PBL
 * 
 * Transfer 1
 */
#define ALT_SDMMC_BMOD_PBL_E_TRANS1     0x0
/*
 * Enumerated value for register field ALT_SDMMC_BMOD_PBL
 * 
 * Transfer 4
 */
#define ALT_SDMMC_BMOD_PBL_E_TRANS4     0x1
/*
 * Enumerated value for register field ALT_SDMMC_BMOD_PBL
 * 
 * Transfer 8
 */
#define ALT_SDMMC_BMOD_PBL_E_TRANS8     0x2
/*
 * Enumerated value for register field ALT_SDMMC_BMOD_PBL
 * 
 * Transfer 16
 */
#define ALT_SDMMC_BMOD_PBL_E_TRANS16    0x3
/*
 * Enumerated value for register field ALT_SDMMC_BMOD_PBL
 * 
 * Transfer 32
 */
#define ALT_SDMMC_BMOD_PBL_E_TRANS32    0x4
/*
 * Enumerated value for register field ALT_SDMMC_BMOD_PBL
 * 
 * Transfer 64
 */
#define ALT_SDMMC_BMOD_PBL_E_TRANS64    0x5
/*
 * Enumerated value for register field ALT_SDMMC_BMOD_PBL
 * 
 * Transfer 128
 */
#define ALT_SDMMC_BMOD_PBL_E_TRANS128   0x6
/*
 * Enumerated value for register field ALT_SDMMC_BMOD_PBL
 * 
 * Transfer 256
 */
#define ALT_SDMMC_BMOD_PBL_E_TRANS256   0x7

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_BMOD_PBL register field. */
#define ALT_SDMMC_BMOD_PBL_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_BMOD_PBL register field. */
#define ALT_SDMMC_BMOD_PBL_MSB        10
/* The width in bits of the ALT_SDMMC_BMOD_PBL register field. */
#define ALT_SDMMC_BMOD_PBL_WIDTH      3
/* The mask used to set the ALT_SDMMC_BMOD_PBL register field value. */
#define ALT_SDMMC_BMOD_PBL_SET_MSK    0x00000700
/* The mask used to clear the ALT_SDMMC_BMOD_PBL register field value. */
#define ALT_SDMMC_BMOD_PBL_CLR_MSK    0xfffff8ff
/* The reset value of the ALT_SDMMC_BMOD_PBL register field. */
#define ALT_SDMMC_BMOD_PBL_RESET      0x0
/* Extracts the ALT_SDMMC_BMOD_PBL field value from a register. */
#define ALT_SDMMC_BMOD_PBL_GET(value) (((value) & 0x00000700) >> 8)
/* Produces a ALT_SDMMC_BMOD_PBL register field value suitable for setting the register. */
#define ALT_SDMMC_BMOD_PBL_SET(value) (((value) << 8) & 0x00000700)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_BMOD.
 */
struct ALT_SDMMC_BMOD_s
{
    uint32_t        swr :  1;  /* Software Reset */
    uint32_t        fb  :  1;  /* Fixed Burst */
    uint32_t        dsl :  5;  /* Descriptor Skip Length */
    uint32_t        de  :  1;  /* IDMAC Enable */
    const uint32_t  pbl :  3;  /* Programmable Burst Length */
    uint32_t            : 21;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_BMOD. */
typedef volatile struct ALT_SDMMC_BMOD_s  ALT_SDMMC_BMOD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_BMOD register from the beginning of the component. */
#define ALT_SDMMC_BMOD_OFST        0x80

/*
 * Register : Poll Demand Register - pldmnd
 * 
 * See Field Description.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [31:0] | W      | 0x0   | Poll Demand
 * 
 */
/*
 * Field : Poll Demand - pd
 * 
 * If the OWN bit of a descriptor is not set, the FSM goes to the Suspend state.
 * The host needs to write any value into this register for the IDMAC FSM to resume
 * normal descriptor fetch operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_PLDMND_PD register field. */
#define ALT_SDMMC_PLDMND_PD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_PLDMND_PD register field. */
#define ALT_SDMMC_PLDMND_PD_MSB        31
/* The width in bits of the ALT_SDMMC_PLDMND_PD register field. */
#define ALT_SDMMC_PLDMND_PD_WIDTH      32
/* The mask used to set the ALT_SDMMC_PLDMND_PD register field value. */
#define ALT_SDMMC_PLDMND_PD_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDMMC_PLDMND_PD register field value. */
#define ALT_SDMMC_PLDMND_PD_CLR_MSK    0x00000000
/* The reset value of the ALT_SDMMC_PLDMND_PD register field. */
#define ALT_SDMMC_PLDMND_PD_RESET      0x0
/* Extracts the ALT_SDMMC_PLDMND_PD field value from a register. */
#define ALT_SDMMC_PLDMND_PD_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDMMC_PLDMND_PD register field value suitable for setting the register. */
#define ALT_SDMMC_PLDMND_PD_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_PLDMND.
 */
struct ALT_SDMMC_PLDMND_s
{
    uint32_t  pd : 32;  /* Poll Demand */
};

/* The typedef declaration for register ALT_SDMMC_PLDMND. */
typedef volatile struct ALT_SDMMC_PLDMND_s  ALT_SDMMC_PLDMND_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_PLDMND register from the beginning of the component. */
#define ALT_SDMMC_PLDMND_OFST        0x84

/*
 * Register : Descriptor List Base Address Register - dbaddr
 * 
 * See Field Descriptor
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description             
 * :-------|:-------|:------|:-------------------------
 *  [1:0]  | ???    | 0x0   | *UNDEFINED*             
 *  [31:2] | RW     | 0x0   | Start of Descriptor List
 * 
 */
/*
 * Field : Start of Descriptor List - sdl
 * 
 * Contains the base address of the First Descriptor. This is the byte address
 * divided by 4.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_DBADDR_SDL register field. */
#define ALT_SDMMC_DBADDR_SDL_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_DBADDR_SDL register field. */
#define ALT_SDMMC_DBADDR_SDL_MSB        31
/* The width in bits of the ALT_SDMMC_DBADDR_SDL register field. */
#define ALT_SDMMC_DBADDR_SDL_WIDTH      30
/* The mask used to set the ALT_SDMMC_DBADDR_SDL register field value. */
#define ALT_SDMMC_DBADDR_SDL_SET_MSK    0xfffffffc
/* The mask used to clear the ALT_SDMMC_DBADDR_SDL register field value. */
#define ALT_SDMMC_DBADDR_SDL_CLR_MSK    0x00000003
/* The reset value of the ALT_SDMMC_DBADDR_SDL register field. */
#define ALT_SDMMC_DBADDR_SDL_RESET      0x0
/* Extracts the ALT_SDMMC_DBADDR_SDL field value from a register. */
#define ALT_SDMMC_DBADDR_SDL_GET(value) (((value) & 0xfffffffc) >> 2)
/* Produces a ALT_SDMMC_DBADDR_SDL register field value suitable for setting the register. */
#define ALT_SDMMC_DBADDR_SDL_SET(value) (((value) << 2) & 0xfffffffc)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_DBADDR.
 */
struct ALT_SDMMC_DBADDR_s
{
    uint32_t      :  2;  /* *UNDEFINED* */
    uint32_t  sdl : 30;  /* Start of Descriptor List */
};

/* The typedef declaration for register ALT_SDMMC_DBADDR. */
typedef volatile struct ALT_SDMMC_DBADDR_s  ALT_SDMMC_DBADDR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_DBADDR register from the beginning of the component. */
#define ALT_SDMMC_DBADDR_OFST        0x88

/*
 * Register : Internal DMAC Status Register - idsts
 * 
 * Sets Internal DMAC Status Fields
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                     
 * :--------|:-------|:------|:---------------------------------
 *  [0]     | RW     | 0x0   | Transmit Interrupt              
 *  [1]     | RW     | 0x0   | Receive Interrupt               
 *  [2]     | RW     | 0x0   | Fatal Bus Error Interrupt       
 *  [3]     | ???    | 0x0   | *UNDEFINED*                     
 *  [4]     | RW     | 0x0   | Descriptor Unavailable Interrupt
 *  [5]     | RW     | 0x0   | Card Error Summary              
 *  [7:6]   | ???    | 0x0   | *UNDEFINED*                     
 *  [8]     | RW     | 0x0   | Normal Interrupt Summary        
 *  [9]     | RW     | 0x0   | Abnormal Interrupt Summary      
 *  [12:10] | R      | 0x0   | Error Bits                      
 *  [16:13] | R      | 0x0   | Finite State Machine            
 *  [31:17] | ???    | 0x0   | *UNDEFINED*                     
 * 
 */
/*
 * Field : Transmit Interrupt - ti
 * 
 * Indicates that data transmission is finished for a descriptor.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                              
 * :---------------------------|:------|:------------------------------------------
 *  ALT_SDMMC_IDSTS_TI_E_CLR   | 0x1   | Clears Transmit Interrupt Status Bit     
 *  ALT_SDMMC_IDSTS_TI_E_NOCLR | 0x0   | No Clear of Transmit Interrupt Status Bit
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_TI
 * 
 * Clears Transmit Interrupt Status Bit
 */
#define ALT_SDMMC_IDSTS_TI_E_CLR    0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_TI
 * 
 * No Clear of Transmit Interrupt Status Bit
 */
#define ALT_SDMMC_IDSTS_TI_E_NOCLR  0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDSTS_TI register field. */
#define ALT_SDMMC_IDSTS_TI_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDSTS_TI register field. */
#define ALT_SDMMC_IDSTS_TI_MSB        0
/* The width in bits of the ALT_SDMMC_IDSTS_TI register field. */
#define ALT_SDMMC_IDSTS_TI_WIDTH      1
/* The mask used to set the ALT_SDMMC_IDSTS_TI register field value. */
#define ALT_SDMMC_IDSTS_TI_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_IDSTS_TI register field value. */
#define ALT_SDMMC_IDSTS_TI_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_IDSTS_TI register field. */
#define ALT_SDMMC_IDSTS_TI_RESET      0x0
/* Extracts the ALT_SDMMC_IDSTS_TI field value from a register. */
#define ALT_SDMMC_IDSTS_TI_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_IDSTS_TI register field value suitable for setting the register. */
#define ALT_SDMMC_IDSTS_TI_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Receive Interrupt - ri
 * 
 * Indicates the completion of data reception for a descriptor
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                             
 * :---------------------------|:------|:-----------------------------------------
 *  ALT_SDMMC_IDSTS_RI_E_CLR   | 0x1   | Clears Receive Interrupt Status Bit     
 *  ALT_SDMMC_IDSTS_RI_E_NOCLR | 0x0   | No Clear of Receive Interrupt Status Bit
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_RI
 * 
 * Clears Receive Interrupt Status Bit
 */
#define ALT_SDMMC_IDSTS_RI_E_CLR    0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_RI
 * 
 * No Clear of Receive Interrupt Status Bit
 */
#define ALT_SDMMC_IDSTS_RI_E_NOCLR  0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDSTS_RI register field. */
#define ALT_SDMMC_IDSTS_RI_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDSTS_RI register field. */
#define ALT_SDMMC_IDSTS_RI_MSB        1
/* The width in bits of the ALT_SDMMC_IDSTS_RI register field. */
#define ALT_SDMMC_IDSTS_RI_WIDTH      1
/* The mask used to set the ALT_SDMMC_IDSTS_RI register field value. */
#define ALT_SDMMC_IDSTS_RI_SET_MSK    0x00000002
/* The mask used to clear the ALT_SDMMC_IDSTS_RI register field value. */
#define ALT_SDMMC_IDSTS_RI_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SDMMC_IDSTS_RI register field. */
#define ALT_SDMMC_IDSTS_RI_RESET      0x0
/* Extracts the ALT_SDMMC_IDSTS_RI field value from a register. */
#define ALT_SDMMC_IDSTS_RI_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SDMMC_IDSTS_RI register field value suitable for setting the register. */
#define ALT_SDMMC_IDSTS_RI_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Fatal Bus Error Interrupt - fbe
 * 
 * Indicates that a Bus Error occurred (IDSTS[12:10]). When setthe DMA disables all
 * its bus accesses.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                                     
 * :----------------------------|:------|:-------------------------------------------------
 *  ALT_SDMMC_IDSTS_FBE_E_CLR   | 0x1   | Clears Fatal Bus Error Interrupt Status Bit     
 *  ALT_SDMMC_IDSTS_FBE_E_NOCLR | 0x0   | No Clear of Fatal Bus Error Interrupt Status Bit
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_FBE
 * 
 * Clears Fatal Bus Error Interrupt Status Bit
 */
#define ALT_SDMMC_IDSTS_FBE_E_CLR   0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_FBE
 * 
 * No Clear of Fatal Bus Error Interrupt Status Bit
 */
#define ALT_SDMMC_IDSTS_FBE_E_NOCLR 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDSTS_FBE register field. */
#define ALT_SDMMC_IDSTS_FBE_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDSTS_FBE register field. */
#define ALT_SDMMC_IDSTS_FBE_MSB        2
/* The width in bits of the ALT_SDMMC_IDSTS_FBE register field. */
#define ALT_SDMMC_IDSTS_FBE_WIDTH      1
/* The mask used to set the ALT_SDMMC_IDSTS_FBE register field value. */
#define ALT_SDMMC_IDSTS_FBE_SET_MSK    0x00000004
/* The mask used to clear the ALT_SDMMC_IDSTS_FBE register field value. */
#define ALT_SDMMC_IDSTS_FBE_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SDMMC_IDSTS_FBE register field. */
#define ALT_SDMMC_IDSTS_FBE_RESET      0x0
/* Extracts the ALT_SDMMC_IDSTS_FBE field value from a register. */
#define ALT_SDMMC_IDSTS_FBE_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SDMMC_IDSTS_FBE register field value suitable for setting the register. */
#define ALT_SDMMC_IDSTS_FBE_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Descriptor Unavailable Interrupt - du
 * 
 * This status bit is set when the descriptor is unavailable due to OWN bit = 0
 * (DES0[31] =0).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description                                   
 * :---------------------------|:------|:-----------------------------------------------
 *  ALT_SDMMC_IDSTS_DU_E_CLR   | 0x1   | Clears Descriptor Unavailable Interrupt Status
 * :                           |       | Bit                                           
 *  ALT_SDMMC_IDSTS_DU_E_NOCLR | 0x0   | No Clear of Descriptor Unavailable Interrupt  
 * :                           |       | Status Bit                                    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_DU
 * 
 * Clears Descriptor Unavailable Interrupt Status Bit
 */
#define ALT_SDMMC_IDSTS_DU_E_CLR    0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_DU
 * 
 * No Clear of Descriptor Unavailable Interrupt Status Bit
 */
#define ALT_SDMMC_IDSTS_DU_E_NOCLR  0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDSTS_DU register field. */
#define ALT_SDMMC_IDSTS_DU_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDSTS_DU register field. */
#define ALT_SDMMC_IDSTS_DU_MSB        4
/* The width in bits of the ALT_SDMMC_IDSTS_DU register field. */
#define ALT_SDMMC_IDSTS_DU_WIDTH      1
/* The mask used to set the ALT_SDMMC_IDSTS_DU register field value. */
#define ALT_SDMMC_IDSTS_DU_SET_MSK    0x00000010
/* The mask used to clear the ALT_SDMMC_IDSTS_DU register field value. */
#define ALT_SDMMC_IDSTS_DU_CLR_MSK    0xffffffef
/* The reset value of the ALT_SDMMC_IDSTS_DU register field. */
#define ALT_SDMMC_IDSTS_DU_RESET      0x0
/* Extracts the ALT_SDMMC_IDSTS_DU field value from a register. */
#define ALT_SDMMC_IDSTS_DU_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SDMMC_IDSTS_DU register field value suitable for setting the register. */
#define ALT_SDMMC_IDSTS_DU_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Card Error Summary - ces
 * 
 * Indicates the status of the transaction to/from the card; also present in
 * RINTSTS. Indicates the logical OR of the following bits:
 * 
 * EBE - End Bit Error
 * 
 * RTO - Response Timeout/Boot Ack Timeout
 * 
 * RCRC - Response CRC
 * 
 * SBE - Start Bit Error
 * 
 * DRTO - Data Read Timeout/BDS timeout
 * 
 * DCRC - Data CRC for Receive
 * 
 * RE - Response Error
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                                     
 * :----------------------------|:------|:-------------------------------------------------
 *  ALT_SDMMC_IDSTS_CES_E_CLR   | 0x1   | Clears Card Error Summary Interrupt Status Bit  
 *  ALT_SDMMC_IDSTS_CES_E_NOCLR | 0x0   | No Clear Card Error Summary Interrupt Status Bit
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_CES
 * 
 * Clears Card Error Summary Interrupt Status Bit
 */
#define ALT_SDMMC_IDSTS_CES_E_CLR   0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_CES
 * 
 * No Clear Card Error Summary Interrupt Status Bit
 */
#define ALT_SDMMC_IDSTS_CES_E_NOCLR 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDSTS_CES register field. */
#define ALT_SDMMC_IDSTS_CES_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDSTS_CES register field. */
#define ALT_SDMMC_IDSTS_CES_MSB        5
/* The width in bits of the ALT_SDMMC_IDSTS_CES register field. */
#define ALT_SDMMC_IDSTS_CES_WIDTH      1
/* The mask used to set the ALT_SDMMC_IDSTS_CES register field value. */
#define ALT_SDMMC_IDSTS_CES_SET_MSK    0x00000020
/* The mask used to clear the ALT_SDMMC_IDSTS_CES register field value. */
#define ALT_SDMMC_IDSTS_CES_CLR_MSK    0xffffffdf
/* The reset value of the ALT_SDMMC_IDSTS_CES register field. */
#define ALT_SDMMC_IDSTS_CES_RESET      0x0
/* Extracts the ALT_SDMMC_IDSTS_CES field value from a register. */
#define ALT_SDMMC_IDSTS_CES_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_SDMMC_IDSTS_CES register field value suitable for setting the register. */
#define ALT_SDMMC_IDSTS_CES_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Normal Interrupt Summary - nis
 * 
 * Logical OR of the following:
 * 
 * IDSTS[0] - Transmit Interrupt
 * 
 * IDSTS[1] - Receive Interrupt
 * 
 * Only unmasked bits affect this bit. This is a sticky bit and must be cleared
 * each time a corresponding bit that causes NIS to be set is cleared.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                                  
 * :----------------------------|:------|:----------------------------------------------
 *  ALT_SDMMC_IDSTS_NIS_E_CLR   | 0x1   | Clears Normal Interrupt Summary  Status Bit  
 *  ALT_SDMMC_IDSTS_NIS_E_NOCLR | 0x0   | No Clear Normal Interrupt Summary  Status Bit
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_NIS
 * 
 * Clears Normal Interrupt Summary  Status Bit
 */
#define ALT_SDMMC_IDSTS_NIS_E_CLR   0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_NIS
 * 
 * No Clear Normal Interrupt Summary  Status Bit
 */
#define ALT_SDMMC_IDSTS_NIS_E_NOCLR 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDSTS_NIS register field. */
#define ALT_SDMMC_IDSTS_NIS_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDSTS_NIS register field. */
#define ALT_SDMMC_IDSTS_NIS_MSB        8
/* The width in bits of the ALT_SDMMC_IDSTS_NIS register field. */
#define ALT_SDMMC_IDSTS_NIS_WIDTH      1
/* The mask used to set the ALT_SDMMC_IDSTS_NIS register field value. */
#define ALT_SDMMC_IDSTS_NIS_SET_MSK    0x00000100
/* The mask used to clear the ALT_SDMMC_IDSTS_NIS register field value. */
#define ALT_SDMMC_IDSTS_NIS_CLR_MSK    0xfffffeff
/* The reset value of the ALT_SDMMC_IDSTS_NIS register field. */
#define ALT_SDMMC_IDSTS_NIS_RESET      0x0
/* Extracts the ALT_SDMMC_IDSTS_NIS field value from a register. */
#define ALT_SDMMC_IDSTS_NIS_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_SDMMC_IDSTS_NIS register field value suitable for setting the register. */
#define ALT_SDMMC_IDSTS_NIS_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Abnormal Interrupt Summary - ais
 * 
 * Logical OR of the following:
 * 
 * IDSTS[2] - Fatal Bus Interrupt
 * 
 * IDSTS[4] - DU bit Interrupt
 * 
 * IDSTS[5] - Card Error Summary Interrupt
 * 
 * Only unmasked bits affect this bit. This is a sticky bit and must be cleared
 * each time a corresponding bit that causes AIS to be set is cleared.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                                   
 * :----------------------------|:------|:-----------------------------------------------
 *  ALT_SDMMC_IDSTS_AIS_E_CLR   | 0x1   | Clears Abnormal Summary Interrupt Status Bit  
 *  ALT_SDMMC_IDSTS_AIS_E_NOCLR | 0x0   | No Clear Abnormal Summary Interrupt Status Bit
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_AIS
 * 
 * Clears Abnormal Summary Interrupt Status Bit
 */
#define ALT_SDMMC_IDSTS_AIS_E_CLR   0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_AIS
 * 
 * No Clear Abnormal Summary Interrupt Status Bit
 */
#define ALT_SDMMC_IDSTS_AIS_E_NOCLR 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDSTS_AIS register field. */
#define ALT_SDMMC_IDSTS_AIS_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDSTS_AIS register field. */
#define ALT_SDMMC_IDSTS_AIS_MSB        9
/* The width in bits of the ALT_SDMMC_IDSTS_AIS register field. */
#define ALT_SDMMC_IDSTS_AIS_WIDTH      1
/* The mask used to set the ALT_SDMMC_IDSTS_AIS register field value. */
#define ALT_SDMMC_IDSTS_AIS_SET_MSK    0x00000200
/* The mask used to clear the ALT_SDMMC_IDSTS_AIS register field value. */
#define ALT_SDMMC_IDSTS_AIS_CLR_MSK    0xfffffdff
/* The reset value of the ALT_SDMMC_IDSTS_AIS register field. */
#define ALT_SDMMC_IDSTS_AIS_RESET      0x0
/* Extracts the ALT_SDMMC_IDSTS_AIS field value from a register. */
#define ALT_SDMMC_IDSTS_AIS_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_SDMMC_IDSTS_AIS register field value suitable for setting the register. */
#define ALT_SDMMC_IDSTS_AIS_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Error Bits - eb
 * 
 * Indicates the type of error that caused a Bus Error. Valid only with Fatal Bus
 * Error bit (IDSTS[2]) set. This field does not generate an interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description                                    
 * :--------------------------------|:------|:------------------------------------------------
 *  ALT_SDMMC_IDSTS_EB_E_HOSTARBTTX | 0x1   | Host Abort during transmission Status Bit      
 *  ALT_SDMMC_IDSTS_EB_E_HOSTARBRX  | 0x2   | Host Abort received during reception Status Bit
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_EB
 * 
 * Host Abort during transmission Status Bit
 */
#define ALT_SDMMC_IDSTS_EB_E_HOSTARBTTX 0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_EB
 * 
 * Host Abort received during reception Status Bit
 */
#define ALT_SDMMC_IDSTS_EB_E_HOSTARBRX  0x2

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDSTS_EB register field. */
#define ALT_SDMMC_IDSTS_EB_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDSTS_EB register field. */
#define ALT_SDMMC_IDSTS_EB_MSB        12
/* The width in bits of the ALT_SDMMC_IDSTS_EB register field. */
#define ALT_SDMMC_IDSTS_EB_WIDTH      3
/* The mask used to set the ALT_SDMMC_IDSTS_EB register field value. */
#define ALT_SDMMC_IDSTS_EB_SET_MSK    0x00001c00
/* The mask used to clear the ALT_SDMMC_IDSTS_EB register field value. */
#define ALT_SDMMC_IDSTS_EB_CLR_MSK    0xffffe3ff
/* The reset value of the ALT_SDMMC_IDSTS_EB register field. */
#define ALT_SDMMC_IDSTS_EB_RESET      0x0
/* Extracts the ALT_SDMMC_IDSTS_EB field value from a register. */
#define ALT_SDMMC_IDSTS_EB_GET(value) (((value) & 0x00001c00) >> 10)
/* Produces a ALT_SDMMC_IDSTS_EB register field value suitable for setting the register. */
#define ALT_SDMMC_IDSTS_EB_SET(value) (((value) << 10) & 0x00001c00)

/*
 * Field : Finite State Machine - fsm
 * 
 * DMAC FSM present state.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description    
 * :-----------------------------------|:------|:----------------
 *  ALT_SDMMC_IDSTS_FSM_E_DMAIDLE      | 0x0   | DMA IDLE       
 *  ALT_SDMMC_IDSTS_FSM_E_DMASUSPEND   | 0x1   | DMA SUSPEND    
 *  ALT_SDMMC_IDSTS_FSM_E_DESCRD       | 0x2   | DESC_RD        
 *  ALT_SDMMC_IDSTS_FSM_E_DESCCHK      | 0x3   | DESC_CHK       
 *  ALT_SDMMC_IDSTS_FSM_E_DMARDREQWAIT | 0x4   | DMA RD REQ WAIT
 *  ALT_SDMMC_IDSTS_FSM_E_DMAWRREQWAIT | 0x5   | DMA WR REQ WAIT
 *  ALT_SDMMC_IDSTS_FSM_E_DMARD        | 0x6   | DMA RD         
 *  ALT_SDMMC_IDSTS_FSM_E_DMAWR        | 0x7   | DMA WR         
 *  ALT_SDMMC_IDSTS_FSM_E_DECCLOSE     | 0x8   | DESC CLOSE     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_FSM
 * 
 * DMA IDLE
 */
#define ALT_SDMMC_IDSTS_FSM_E_DMAIDLE       0x0
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_FSM
 * 
 * DMA SUSPEND
 */
#define ALT_SDMMC_IDSTS_FSM_E_DMASUSPEND    0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_FSM
 * 
 * DESC_RD
 */
#define ALT_SDMMC_IDSTS_FSM_E_DESCRD        0x2
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_FSM
 * 
 * DESC_CHK
 */
#define ALT_SDMMC_IDSTS_FSM_E_DESCCHK       0x3
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_FSM
 * 
 * DMA RD REQ WAIT
 */
#define ALT_SDMMC_IDSTS_FSM_E_DMARDREQWAIT  0x4
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_FSM
 * 
 * DMA WR REQ WAIT
 */
#define ALT_SDMMC_IDSTS_FSM_E_DMAWRREQWAIT  0x5
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_FSM
 * 
 * DMA RD
 */
#define ALT_SDMMC_IDSTS_FSM_E_DMARD         0x6
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_FSM
 * 
 * DMA WR
 */
#define ALT_SDMMC_IDSTS_FSM_E_DMAWR         0x7
/*
 * Enumerated value for register field ALT_SDMMC_IDSTS_FSM
 * 
 * DESC CLOSE
 */
#define ALT_SDMMC_IDSTS_FSM_E_DECCLOSE      0x8

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDSTS_FSM register field. */
#define ALT_SDMMC_IDSTS_FSM_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDSTS_FSM register field. */
#define ALT_SDMMC_IDSTS_FSM_MSB        16
/* The width in bits of the ALT_SDMMC_IDSTS_FSM register field. */
#define ALT_SDMMC_IDSTS_FSM_WIDTH      4
/* The mask used to set the ALT_SDMMC_IDSTS_FSM register field value. */
#define ALT_SDMMC_IDSTS_FSM_SET_MSK    0x0001e000
/* The mask used to clear the ALT_SDMMC_IDSTS_FSM register field value. */
#define ALT_SDMMC_IDSTS_FSM_CLR_MSK    0xfffe1fff
/* The reset value of the ALT_SDMMC_IDSTS_FSM register field. */
#define ALT_SDMMC_IDSTS_FSM_RESET      0x0
/* Extracts the ALT_SDMMC_IDSTS_FSM field value from a register. */
#define ALT_SDMMC_IDSTS_FSM_GET(value) (((value) & 0x0001e000) >> 13)
/* Produces a ALT_SDMMC_IDSTS_FSM register field value suitable for setting the register. */
#define ALT_SDMMC_IDSTS_FSM_SET(value) (((value) << 13) & 0x0001e000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_IDSTS.
 */
struct ALT_SDMMC_IDSTS_s
{
    uint32_t        ti  :  1;  /* Transmit Interrupt */
    uint32_t        ri  :  1;  /* Receive Interrupt */
    uint32_t        fbe :  1;  /* Fatal Bus Error Interrupt */
    uint32_t            :  1;  /* *UNDEFINED* */
    uint32_t        du  :  1;  /* Descriptor Unavailable Interrupt */
    uint32_t        ces :  1;  /* Card Error Summary */
    uint32_t            :  2;  /* *UNDEFINED* */
    uint32_t        nis :  1;  /* Normal Interrupt Summary */
    uint32_t        ais :  1;  /* Abnormal Interrupt Summary */
    const uint32_t  eb  :  3;  /* Error Bits */
    const uint32_t  fsm :  4;  /* Finite State Machine */
    uint32_t            : 15;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_IDSTS. */
typedef volatile struct ALT_SDMMC_IDSTS_s  ALT_SDMMC_IDSTS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_IDSTS register from the beginning of the component. */
#define ALT_SDMMC_IDSTS_OFST        0x8c

/*
 * Register : Internal DMAC Interrupt Enable Register - idinten
 * 
 * Various DMA Interrupt Enable Status
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                        
 * :--------|:-------|:------|:------------------------------------
 *  [0]     | RW     | 0x0   | Transmit Interrupt Enable          
 *  [1]     | RW     | 0x0   | Receive Interrupt Enable           
 *  [2]     | RW     | 0x0   | Fatal Bus Error                    
 *  [3]     | ???    | 0x0   | *UNDEFINED*                        
 *  [4]     | RW     | 0x0   | Descriptor Unavailable Interrupt   
 *  [5]     | RW     | 0x0   | Card Error Summary Interrupt Enable
 *  [7:6]   | ???    | 0x0   | *UNDEFINED*                        
 *  [8]     | RW     | 0x0   | Normal Interrupt Summary Enable    
 *  [9]     | RW     | 0x0   | Abnormal Interrupt Summary Enable. 
 *  [31:10] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : Transmit Interrupt Enable - ti
 * 
 * Enables and Disables Transmit Interrupt when Normal Interrupt Summary Enable is
 * set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                   
 * :----------------------------|:------|:-------------------------------
 *  ALT_SDMMC_IDINTEN_TI_E_END  | 0x1   | Transmit Interrupt is enabled 
 *  ALT_SDMMC_IDINTEN_TI_E_DISD | 0x0   | Transmit Interrupt is disabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDINTEN_TI
 * 
 * Transmit Interrupt is enabled
 */
#define ALT_SDMMC_IDINTEN_TI_E_END  0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDINTEN_TI
 * 
 * Transmit Interrupt is disabled
 */
#define ALT_SDMMC_IDINTEN_TI_E_DISD 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDINTEN_TI register field. */
#define ALT_SDMMC_IDINTEN_TI_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDINTEN_TI register field. */
#define ALT_SDMMC_IDINTEN_TI_MSB        0
/* The width in bits of the ALT_SDMMC_IDINTEN_TI register field. */
#define ALT_SDMMC_IDINTEN_TI_WIDTH      1
/* The mask used to set the ALT_SDMMC_IDINTEN_TI register field value. */
#define ALT_SDMMC_IDINTEN_TI_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_IDINTEN_TI register field value. */
#define ALT_SDMMC_IDINTEN_TI_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_IDINTEN_TI register field. */
#define ALT_SDMMC_IDINTEN_TI_RESET      0x0
/* Extracts the ALT_SDMMC_IDINTEN_TI field value from a register. */
#define ALT_SDMMC_IDINTEN_TI_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_IDINTEN_TI register field value suitable for setting the register. */
#define ALT_SDMMC_IDINTEN_TI_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Receive Interrupt Enable - ri
 * 
 * Enables and Disables Receive Interrupt  when Normal Interrupt Summary Enable is
 * set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                  
 * :----------------------------|:------|:------------------------------
 *  ALT_SDMMC_IDINTEN_RI_E_END  | 0x1   | Receive Interrupt is enabled 
 *  ALT_SDMMC_IDINTEN_RI_E_DISD | 0x0   | Receive Interrupt is disabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDINTEN_RI
 * 
 * Receive Interrupt is enabled
 */
#define ALT_SDMMC_IDINTEN_RI_E_END  0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDINTEN_RI
 * 
 * Receive Interrupt is disabled
 */
#define ALT_SDMMC_IDINTEN_RI_E_DISD 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDINTEN_RI register field. */
#define ALT_SDMMC_IDINTEN_RI_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDINTEN_RI register field. */
#define ALT_SDMMC_IDINTEN_RI_MSB        1
/* The width in bits of the ALT_SDMMC_IDINTEN_RI register field. */
#define ALT_SDMMC_IDINTEN_RI_WIDTH      1
/* The mask used to set the ALT_SDMMC_IDINTEN_RI register field value. */
#define ALT_SDMMC_IDINTEN_RI_SET_MSK    0x00000002
/* The mask used to clear the ALT_SDMMC_IDINTEN_RI register field value. */
#define ALT_SDMMC_IDINTEN_RI_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SDMMC_IDINTEN_RI register field. */
#define ALT_SDMMC_IDINTEN_RI_RESET      0x0
/* Extracts the ALT_SDMMC_IDINTEN_RI field value from a register. */
#define ALT_SDMMC_IDINTEN_RI_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SDMMC_IDINTEN_RI register field value suitable for setting the register. */
#define ALT_SDMMC_IDINTEN_RI_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Fatal Bus Error - fbe
 * 
 * When set with Abnormal Interrupt Summary Enable, the Fatal Bus Error Interrupt
 * is enabled.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description                          
 * :-----------------------------|:------|:--------------------------------------
 *  ALT_SDMMC_IDINTEN_FBE_E_END  | 0x1   | Fatal Bus Error Interrupt is enabled 
 *  ALT_SDMMC_IDINTEN_FBE_E_DISD | 0x0   | Fatal Bus Error Interrupt is disabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDINTEN_FBE
 * 
 * Fatal Bus Error Interrupt is enabled
 */
#define ALT_SDMMC_IDINTEN_FBE_E_END     0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDINTEN_FBE
 * 
 * Fatal Bus Error Interrupt is disabled
 */
#define ALT_SDMMC_IDINTEN_FBE_E_DISD    0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDINTEN_FBE register field. */
#define ALT_SDMMC_IDINTEN_FBE_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDINTEN_FBE register field. */
#define ALT_SDMMC_IDINTEN_FBE_MSB        2
/* The width in bits of the ALT_SDMMC_IDINTEN_FBE register field. */
#define ALT_SDMMC_IDINTEN_FBE_WIDTH      1
/* The mask used to set the ALT_SDMMC_IDINTEN_FBE register field value. */
#define ALT_SDMMC_IDINTEN_FBE_SET_MSK    0x00000004
/* The mask used to clear the ALT_SDMMC_IDINTEN_FBE register field value. */
#define ALT_SDMMC_IDINTEN_FBE_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SDMMC_IDINTEN_FBE register field. */
#define ALT_SDMMC_IDINTEN_FBE_RESET      0x0
/* Extracts the ALT_SDMMC_IDINTEN_FBE field value from a register. */
#define ALT_SDMMC_IDINTEN_FBE_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SDMMC_IDINTEN_FBE register field value suitable for setting the register. */
#define ALT_SDMMC_IDINTEN_FBE_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Descriptor Unavailable Interrupt - du
 * 
 * When set along with Abnormal Interrupt Summary Enable, the DU interrupt is
 * enabled.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                                 
 * :----------------------------|:------|:---------------------------------------------
 *  ALT_SDMMC_IDINTEN_DU_E_END  | 0x1   | Descriptor Unavailable Interrupt is enabled 
 *  ALT_SDMMC_IDINTEN_DU_E_DISD | 0x0   | Descriptor Unavailable Interrupt is disabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDINTEN_DU
 * 
 * Descriptor Unavailable Interrupt is enabled
 */
#define ALT_SDMMC_IDINTEN_DU_E_END  0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDINTEN_DU
 * 
 * Descriptor Unavailable Interrupt is disabled
 */
#define ALT_SDMMC_IDINTEN_DU_E_DISD 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDINTEN_DU register field. */
#define ALT_SDMMC_IDINTEN_DU_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDINTEN_DU register field. */
#define ALT_SDMMC_IDINTEN_DU_MSB        4
/* The width in bits of the ALT_SDMMC_IDINTEN_DU register field. */
#define ALT_SDMMC_IDINTEN_DU_WIDTH      1
/* The mask used to set the ALT_SDMMC_IDINTEN_DU register field value. */
#define ALT_SDMMC_IDINTEN_DU_SET_MSK    0x00000010
/* The mask used to clear the ALT_SDMMC_IDINTEN_DU register field value. */
#define ALT_SDMMC_IDINTEN_DU_CLR_MSK    0xffffffef
/* The reset value of the ALT_SDMMC_IDINTEN_DU register field. */
#define ALT_SDMMC_IDINTEN_DU_RESET      0x0
/* Extracts the ALT_SDMMC_IDINTEN_DU field value from a register. */
#define ALT_SDMMC_IDINTEN_DU_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SDMMC_IDINTEN_DU register field value suitable for setting the register. */
#define ALT_SDMMC_IDINTEN_DU_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Card Error Summary Interrupt Enable - ces
 * 
 * Enable and disable Card Error Interrupt Summary
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description                             
 * :-----------------------------|:------|:-----------------------------------------
 *  ALT_SDMMC_IDINTEN_CES_E_END  | 0x1   | Card Error Summary Interrupt is enabled 
 *  ALT_SDMMC_IDINTEN_CES_E_DISD | 0x0   | Card Error Summary Interrupt is disabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDINTEN_CES
 * 
 * Card Error Summary Interrupt is enabled
 */
#define ALT_SDMMC_IDINTEN_CES_E_END     0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDINTEN_CES
 * 
 * Card Error Summary Interrupt is disabled
 */
#define ALT_SDMMC_IDINTEN_CES_E_DISD    0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDINTEN_CES register field. */
#define ALT_SDMMC_IDINTEN_CES_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDINTEN_CES register field. */
#define ALT_SDMMC_IDINTEN_CES_MSB        5
/* The width in bits of the ALT_SDMMC_IDINTEN_CES register field. */
#define ALT_SDMMC_IDINTEN_CES_WIDTH      1
/* The mask used to set the ALT_SDMMC_IDINTEN_CES register field value. */
#define ALT_SDMMC_IDINTEN_CES_SET_MSK    0x00000020
/* The mask used to clear the ALT_SDMMC_IDINTEN_CES register field value. */
#define ALT_SDMMC_IDINTEN_CES_CLR_MSK    0xffffffdf
/* The reset value of the ALT_SDMMC_IDINTEN_CES register field. */
#define ALT_SDMMC_IDINTEN_CES_RESET      0x0
/* Extracts the ALT_SDMMC_IDINTEN_CES field value from a register. */
#define ALT_SDMMC_IDINTEN_CES_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_SDMMC_IDINTEN_CES register field value suitable for setting the register. */
#define ALT_SDMMC_IDINTEN_CES_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Normal Interrupt Summary Enable - ni
 * 
 * Enable and Disable Normal Interrupt Summary
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                         
 * :----------------------------|:------|:-------------------------------------
 *  ALT_SDMMC_IDINTEN_NI_E_END  | 0x1   | Normal Interrupt Summary is enabled 
 *  ALT_SDMMC_IDINTEN_NI_E_DISD | 0x0   | Normal Interrupt Summary is disabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDINTEN_NI
 * 
 * Normal Interrupt Summary is enabled
 */
#define ALT_SDMMC_IDINTEN_NI_E_END  0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDINTEN_NI
 * 
 * Normal Interrupt Summary is disabled
 */
#define ALT_SDMMC_IDINTEN_NI_E_DISD 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDINTEN_NI register field. */
#define ALT_SDMMC_IDINTEN_NI_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDINTEN_NI register field. */
#define ALT_SDMMC_IDINTEN_NI_MSB        8
/* The width in bits of the ALT_SDMMC_IDINTEN_NI register field. */
#define ALT_SDMMC_IDINTEN_NI_WIDTH      1
/* The mask used to set the ALT_SDMMC_IDINTEN_NI register field value. */
#define ALT_SDMMC_IDINTEN_NI_SET_MSK    0x00000100
/* The mask used to clear the ALT_SDMMC_IDINTEN_NI register field value. */
#define ALT_SDMMC_IDINTEN_NI_CLR_MSK    0xfffffeff
/* The reset value of the ALT_SDMMC_IDINTEN_NI register field. */
#define ALT_SDMMC_IDINTEN_NI_RESET      0x0
/* Extracts the ALT_SDMMC_IDINTEN_NI field value from a register. */
#define ALT_SDMMC_IDINTEN_NI_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_SDMMC_IDINTEN_NI register field value suitable for setting the register. */
#define ALT_SDMMC_IDINTEN_NI_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Abnormal Interrupt Summary Enable. - ai
 * 
 * This bit enables the following bits:
 * 
 * IDINTEN[2] - Fatal Bus Error Interrupt
 * 
 * IDINTEN[4] - DU Interrupt
 * 
 * IDINTEN[5] - Card Error Summary Interrupt
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                           
 * :----------------------------|:------|:---------------------------------------
 *  ALT_SDMMC_IDINTEN_AI_E_END  | 0x1   | Abnormal Interrupt Summary is enabled 
 *  ALT_SDMMC_IDINTEN_AI_E_DISD | 0x0   | Abnormal Interrupt Summary is disabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_IDINTEN_AI
 * 
 * Abnormal Interrupt Summary is enabled
 */
#define ALT_SDMMC_IDINTEN_AI_E_END  0x1
/*
 * Enumerated value for register field ALT_SDMMC_IDINTEN_AI
 * 
 * Abnormal Interrupt Summary is disabled
 */
#define ALT_SDMMC_IDINTEN_AI_E_DISD 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_IDINTEN_AI register field. */
#define ALT_SDMMC_IDINTEN_AI_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_IDINTEN_AI register field. */
#define ALT_SDMMC_IDINTEN_AI_MSB        9
/* The width in bits of the ALT_SDMMC_IDINTEN_AI register field. */
#define ALT_SDMMC_IDINTEN_AI_WIDTH      1
/* The mask used to set the ALT_SDMMC_IDINTEN_AI register field value. */
#define ALT_SDMMC_IDINTEN_AI_SET_MSK    0x00000200
/* The mask used to clear the ALT_SDMMC_IDINTEN_AI register field value. */
#define ALT_SDMMC_IDINTEN_AI_CLR_MSK    0xfffffdff
/* The reset value of the ALT_SDMMC_IDINTEN_AI register field. */
#define ALT_SDMMC_IDINTEN_AI_RESET      0x0
/* Extracts the ALT_SDMMC_IDINTEN_AI field value from a register. */
#define ALT_SDMMC_IDINTEN_AI_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_SDMMC_IDINTEN_AI register field value suitable for setting the register. */
#define ALT_SDMMC_IDINTEN_AI_SET(value) (((value) << 9) & 0x00000200)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_IDINTEN.
 */
struct ALT_SDMMC_IDINTEN_s
{
    uint32_t  ti  :  1;  /* Transmit Interrupt Enable */
    uint32_t  ri  :  1;  /* Receive Interrupt Enable */
    uint32_t  fbe :  1;  /* Fatal Bus Error */
    uint32_t      :  1;  /* *UNDEFINED* */
    uint32_t  du  :  1;  /* Descriptor Unavailable Interrupt */
    uint32_t  ces :  1;  /* Card Error Summary Interrupt Enable */
    uint32_t      :  2;  /* *UNDEFINED* */
    uint32_t  ni  :  1;  /* Normal Interrupt Summary Enable */
    uint32_t  ai  :  1;  /* Abnormal Interrupt Summary Enable. */
    uint32_t      : 22;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_IDINTEN. */
typedef volatile struct ALT_SDMMC_IDINTEN_s  ALT_SDMMC_IDINTEN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_IDINTEN register from the beginning of the component. */
#define ALT_SDMMC_IDINTEN_OFST        0x90

/*
 * Register : Current Host Descriptor Address Register - dscaddr
 * 
 * See Field Description.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                             
 * :-------|:-------|:------|:-----------------------------------------
 *  [31:0] | R      | 0x0   | Current Host Descriptor Address Register
 * 
 */
/*
 * Field : Current Host Descriptor Address Register - hda
 * 
 * Cleared on reset. Pointer updated by IDMAC during operation. This register
 * points to the start address of the current descriptor read by the IDMAC.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_DSCADDR_HDA register field. */
#define ALT_SDMMC_DSCADDR_HDA_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_DSCADDR_HDA register field. */
#define ALT_SDMMC_DSCADDR_HDA_MSB        31
/* The width in bits of the ALT_SDMMC_DSCADDR_HDA register field. */
#define ALT_SDMMC_DSCADDR_HDA_WIDTH      32
/* The mask used to set the ALT_SDMMC_DSCADDR_HDA register field value. */
#define ALT_SDMMC_DSCADDR_HDA_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDMMC_DSCADDR_HDA register field value. */
#define ALT_SDMMC_DSCADDR_HDA_CLR_MSK    0x00000000
/* The reset value of the ALT_SDMMC_DSCADDR_HDA register field. */
#define ALT_SDMMC_DSCADDR_HDA_RESET      0x0
/* Extracts the ALT_SDMMC_DSCADDR_HDA field value from a register. */
#define ALT_SDMMC_DSCADDR_HDA_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDMMC_DSCADDR_HDA register field value suitable for setting the register. */
#define ALT_SDMMC_DSCADDR_HDA_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_DSCADDR.
 */
struct ALT_SDMMC_DSCADDR_s
{
    const uint32_t  hda : 32;  /* Current Host Descriptor Address Register */
};

/* The typedef declaration for register ALT_SDMMC_DSCADDR. */
typedef volatile struct ALT_SDMMC_DSCADDR_s  ALT_SDMMC_DSCADDR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_DSCADDR register from the beginning of the component. */
#define ALT_SDMMC_DSCADDR_OFST        0x94

/*
 * Register : Current Buffer Descriptor Address Register - bufaddr
 * 
 * See Field Description.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                
 * :-------|:-------|:------|:----------------------------
 *  [31:0] | R      | 0x0   | Host Buffer Address Pointer
 * 
 */
/*
 * Field : Host Buffer Address Pointer - hba
 * 
 * Cleared on Reset. Pointer updated by IDMAC during operation. This register
 * points to the current Data Buffer Address being accessed by the IDMAC.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_BUFADDR_HBA register field. */
#define ALT_SDMMC_BUFADDR_HBA_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_BUFADDR_HBA register field. */
#define ALT_SDMMC_BUFADDR_HBA_MSB        31
/* The width in bits of the ALT_SDMMC_BUFADDR_HBA register field. */
#define ALT_SDMMC_BUFADDR_HBA_WIDTH      32
/* The mask used to set the ALT_SDMMC_BUFADDR_HBA register field value. */
#define ALT_SDMMC_BUFADDR_HBA_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDMMC_BUFADDR_HBA register field value. */
#define ALT_SDMMC_BUFADDR_HBA_CLR_MSK    0x00000000
/* The reset value of the ALT_SDMMC_BUFADDR_HBA register field. */
#define ALT_SDMMC_BUFADDR_HBA_RESET      0x0
/* Extracts the ALT_SDMMC_BUFADDR_HBA field value from a register. */
#define ALT_SDMMC_BUFADDR_HBA_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDMMC_BUFADDR_HBA register field value suitable for setting the register. */
#define ALT_SDMMC_BUFADDR_HBA_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_BUFADDR.
 */
struct ALT_SDMMC_BUFADDR_s
{
    const uint32_t  hba : 32;  /* Host Buffer Address Pointer */
};

/* The typedef declaration for register ALT_SDMMC_BUFADDR. */
typedef volatile struct ALT_SDMMC_BUFADDR_s  ALT_SDMMC_BUFADDR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_BUFADDR register from the beginning of the component. */
#define ALT_SDMMC_BUFADDR_OFST        0x98

/*
 * Register : Card Threshold Control Register - cardthrctl
 * 
 * See Field descriptions
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description               
 * :--------|:-------|:------|:---------------------------
 *  [0]     | RW     | 0x0   | Card Read Threshold Enable
 *  [15:1]  | ???    | 0x0   | *UNDEFINED*               
 *  [27:16] | RW     | 0x0   | Card Read Threshold       
 *  [31:28] | ???    | 0x0   | *UNDEFINED*               
 * 
 */
/*
 * Field : Card Read Threshold Enable - cardrdthren
 * 
 * Host Controller initiates Read Transfer only if CardRdThreshold amount of space
 * is available in receive FIFO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                    | Value | Description                    
 * :----------------------------------------|:------|:--------------------------------
 *  ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_E_END  | 0x1   | Card Read Threshold is enabled 
 *  ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_E_DISD | 0x0   | Card Read Threshold is disabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_CARDTHRCTL_CARDRDTHREN
 * 
 * Card Read Threshold is enabled
 */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_E_END  0x1
/*
 * Enumerated value for register field ALT_SDMMC_CARDTHRCTL_CARDRDTHREN
 * 
 * Card Read Threshold is disabled
 */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_E_DISD 0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CARDTHRCTL_CARDRDTHREN register field. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CARDTHRCTL_CARDRDTHREN register field. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_MSB        0
/* The width in bits of the ALT_SDMMC_CARDTHRCTL_CARDRDTHREN register field. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_WIDTH      1
/* The mask used to set the ALT_SDMMC_CARDTHRCTL_CARDRDTHREN register field value. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDMMC_CARDTHRCTL_CARDRDTHREN register field value. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDMMC_CARDTHRCTL_CARDRDTHREN register field. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_RESET      0x0
/* Extracts the ALT_SDMMC_CARDTHRCTL_CARDRDTHREN field value from a register. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDMMC_CARDTHRCTL_CARDRDTHREN register field value suitable for setting the register. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHREN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Card Read Threshold - cardrdthreshold
 * 
 * Card Read Threshold size
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD register field. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD register field. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD_MSB        27
/* The width in bits of the ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD register field. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD_WIDTH      12
/* The mask used to set the ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD register field value. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD register field value. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD_CLR_MSK    0xf000ffff
/* The reset value of the ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD register field. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD_RESET      0x0
/* Extracts the ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD field value from a register. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD register field value suitable for setting the register. */
#define ALT_SDMMC_CARDTHRCTL_CARDRDTHRESHOLD_SET(value) (((value) << 16) & 0x0fff0000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_CARDTHRCTL.
 */
struct ALT_SDMMC_CARDTHRCTL_s
{
    uint32_t  cardrdthren     :  1;  /* Card Read Threshold Enable */
    uint32_t                  : 15;  /* *UNDEFINED* */
    uint32_t  cardrdthreshold : 12;  /* Card Read Threshold */
    uint32_t                  :  4;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_CARDTHRCTL. */
typedef volatile struct ALT_SDMMC_CARDTHRCTL_s  ALT_SDMMC_CARDTHRCTL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_CARDTHRCTL register from the beginning of the component. */
#define ALT_SDMMC_CARDTHRCTL_OFST        0x100

/*
 * Register : Back End Power Register - back_end_power_r
 * 
 * See Field Description
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description   
 * :--------|:-------|:------|:---------------
 *  [15:0]  | RW     | 0x0   | Back End Power
 *  [31:16] | ???    | 0x0   | *UNDEFINED*   
 * 
 */
/*
 * Field : Back End Power - back_end_power
 * 
 * Back end power operation.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                 | Value | Description                                
 * :-----------------------------------------------------|:------|:--------------------------------------------
 *  ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER_E_BACKEND1 | 0x1   | Back-end Power supplied to card only 1 card
 *  ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER_E_BACKEND0 | 0x0   | Off Reset                                  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER
 * 
 * Back-end Power supplied to card only 1 card
 */
#define ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER_E_BACKEND1    0x1
/*
 * Enumerated value for register field ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER
 * 
 * Off Reset
 */
#define ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER_E_BACKEND0    0x0

/* The Least Significant Bit (LSB) position of the ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER register field. */
#define ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER register field. */
#define ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER_MSB        15
/* The width in bits of the ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER register field. */
#define ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER_WIDTH      16
/* The mask used to set the ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER register field value. */
#define ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER register field value. */
#define ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER_CLR_MSK    0xffff0000
/* The reset value of the ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER register field. */
#define ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER_RESET      0x0
/* Extracts the ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER field value from a register. */
#define ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER register field value suitable for setting the register. */
#define ALT_SDMMC_BACK_END_POWER_R_BACK_END_POWER_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_BACK_END_POWER_R.
 */
struct ALT_SDMMC_BACK_END_POWER_R_s
{
    uint32_t  back_end_power : 16;  /* Back End Power */
    uint32_t                 : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDMMC_BACK_END_POWER_R. */
typedef volatile struct ALT_SDMMC_BACK_END_POWER_R_s  ALT_SDMMC_BACK_END_POWER_R_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_BACK_END_POWER_R register from the beginning of the component. */
#define ALT_SDMMC_BACK_END_POWER_R_OFST        0x104

/*
 * Register : Data FIFO Access - data
 * 
 * Provides read/write access to data FIFO. Addresses 0x200 and above are mapped to
 * the data FIFO. More than one address is mapped to data FIFO so that FIFO can be
 * accessed using bursts.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description
 * :-------|:-------|:--------|:------------
 *  [31:0] | RW     | Unknown | FIFO Data  
 * 
 */
/*
 * Field : FIFO Data - value
 * 
 * Provides read/write access to data FIFO.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDMMC_DATA_VALUE register field. */
#define ALT_SDMMC_DATA_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDMMC_DATA_VALUE register field. */
#define ALT_SDMMC_DATA_VALUE_MSB        31
/* The width in bits of the ALT_SDMMC_DATA_VALUE register field. */
#define ALT_SDMMC_DATA_VALUE_WIDTH      32
/* The mask used to set the ALT_SDMMC_DATA_VALUE register field value. */
#define ALT_SDMMC_DATA_VALUE_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDMMC_DATA_VALUE register field value. */
#define ALT_SDMMC_DATA_VALUE_CLR_MSK    0x00000000
/* The reset value of the ALT_SDMMC_DATA_VALUE register field is UNKNOWN. */
#define ALT_SDMMC_DATA_VALUE_RESET      0x0
/* Extracts the ALT_SDMMC_DATA_VALUE field value from a register. */
#define ALT_SDMMC_DATA_VALUE_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDMMC_DATA_VALUE register field value suitable for setting the register. */
#define ALT_SDMMC_DATA_VALUE_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDMMC_DATA.
 */
struct ALT_SDMMC_DATA_s
{
    uint32_t  value : 32;  /* FIFO Data */
};

/* The typedef declaration for register ALT_SDMMC_DATA. */
typedef volatile struct ALT_SDMMC_DATA_s  ALT_SDMMC_DATA_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDMMC_DATA register from the beginning of the component. */
#define ALT_SDMMC_DATA_OFST        0x200

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_SDMMC.
 */
struct ALT_SDMMC_s
{
    volatile ALT_SDMMC_CTL_t               ctrl;                   /* ALT_SDMMC_CTL */
    volatile ALT_SDMMC_PWREN_t             pwren;                  /* ALT_SDMMC_PWREN */
    volatile ALT_SDMMC_CLKDIV_t            clkdiv;                 /* ALT_SDMMC_CLKDIV */
    volatile ALT_SDMMC_CLKSRC_t            clksrc;                 /* ALT_SDMMC_CLKSRC */
    volatile ALT_SDMMC_CLKENA_t            clkena;                 /* ALT_SDMMC_CLKENA */
    volatile ALT_SDMMC_TMOUT_t             tmout;                  /* ALT_SDMMC_TMOUT */
    volatile ALT_SDMMC_CTYPE_t             ctype;                  /* ALT_SDMMC_CTYPE */
    volatile ALT_SDMMC_BLKSIZ_t            blksiz;                 /* ALT_SDMMC_BLKSIZ */
    volatile ALT_SDMMC_BYTCNT_t            bytcnt;                 /* ALT_SDMMC_BYTCNT */
    volatile ALT_SDMMC_INTMSK_t            intmask;                /* ALT_SDMMC_INTMSK */
    volatile ALT_SDMMC_CMDARG_t            cmdarg;                 /* ALT_SDMMC_CMDARG */
    volatile ALT_SDMMC_CMD_t               cmd;                    /* ALT_SDMMC_CMD */
    volatile ALT_SDMMC_RESP0_t             resp0;                  /* ALT_SDMMC_RESP0 */
    volatile ALT_SDMMC_RESP1_t             resp1;                  /* ALT_SDMMC_RESP1 */
    volatile ALT_SDMMC_RESP2_t             resp2;                  /* ALT_SDMMC_RESP2 */
    volatile ALT_SDMMC_RESP3_t             resp3;                  /* ALT_SDMMC_RESP3 */
    volatile ALT_SDMMC_MINTSTS_t           mintsts;                /* ALT_SDMMC_MINTSTS */
    volatile ALT_SDMMC_RINTSTS_t           rintsts;                /* ALT_SDMMC_RINTSTS */
    volatile ALT_SDMMC_STAT_t              status;                 /* ALT_SDMMC_STAT */
    volatile ALT_SDMMC_FIFOTH_t            fifoth;                 /* ALT_SDMMC_FIFOTH */
    volatile ALT_SDMMC_CDETECT_t           cdetect;                /* ALT_SDMMC_CDETECT */
    volatile ALT_SDMMC_WRTPRT_t            wrtprt;                 /* ALT_SDMMC_WRTPRT */
    volatile uint32_t                      _pad_0x58_0x5b;         /* *UNDEFINED* */
    volatile ALT_SDMMC_TCBCNT_t            tcbcnt;                 /* ALT_SDMMC_TCBCNT */
    volatile ALT_SDMMC_TBBCNT_t            tbbcnt;                 /* ALT_SDMMC_TBBCNT */
    volatile ALT_SDMMC_DEBNCE_t            debnce;                 /* ALT_SDMMC_DEBNCE */
    volatile ALT_SDMMC_USRID_t             usrid;                  /* ALT_SDMMC_USRID */
    volatile ALT_SDMMC_VERID_t             verid;                  /* ALT_SDMMC_VERID */
    volatile ALT_SDMMC_HCON_t              hcon;                   /* ALT_SDMMC_HCON */
    volatile ALT_SDMMC_UHS_REG_t           uhs_reg;                /* ALT_SDMMC_UHS_REG */
    volatile ALT_SDMMC_RST_N_t             rst_n;                  /* ALT_SDMMC_RST_N */
    volatile uint32_t                      _pad_0x7c_0x7f;         /* *UNDEFINED* */
    volatile ALT_SDMMC_BMOD_t              bmod;                   /* ALT_SDMMC_BMOD */
    volatile ALT_SDMMC_PLDMND_t            pldmnd;                 /* ALT_SDMMC_PLDMND */
    volatile ALT_SDMMC_DBADDR_t            dbaddr;                 /* ALT_SDMMC_DBADDR */
    volatile ALT_SDMMC_IDSTS_t             idsts;                  /* ALT_SDMMC_IDSTS */
    volatile ALT_SDMMC_IDINTEN_t           idinten;                /* ALT_SDMMC_IDINTEN */
    volatile ALT_SDMMC_DSCADDR_t           dscaddr;                /* ALT_SDMMC_DSCADDR */
    volatile ALT_SDMMC_BUFADDR_t           bufaddr;                /* ALT_SDMMC_BUFADDR */
    volatile uint32_t                      _pad_0x9c_0xff[25];     /* *UNDEFINED* */
    volatile ALT_SDMMC_CARDTHRCTL_t        cardthrctl;             /* ALT_SDMMC_CARDTHRCTL */
    volatile ALT_SDMMC_BACK_END_POWER_R_t  back_end_power_r;       /* ALT_SDMMC_BACK_END_POWER_R */
    volatile uint32_t                      _pad_0x108_0x1ff[62];   /* *UNDEFINED* */
    volatile ALT_SDMMC_DATA_t              data;                   /* ALT_SDMMC_DATA */
    volatile uint32_t                      _pad_0x204_0x400[127];  /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_SDMMC. */
typedef volatile struct ALT_SDMMC_s  ALT_SDMMC_t;
/* The struct declaration for the raw register contents of register group ALT_SDMMC. */
struct ALT_SDMMC_raw_s
{
    volatile uint32_t  ctrl;                   /* ALT_SDMMC_CTL */
    volatile uint32_t  pwren;                  /* ALT_SDMMC_PWREN */
    volatile uint32_t  clkdiv;                 /* ALT_SDMMC_CLKDIV */
    volatile uint32_t  clksrc;                 /* ALT_SDMMC_CLKSRC */
    volatile uint32_t  clkena;                 /* ALT_SDMMC_CLKENA */
    volatile uint32_t  tmout;                  /* ALT_SDMMC_TMOUT */
    volatile uint32_t  ctype;                  /* ALT_SDMMC_CTYPE */
    volatile uint32_t  blksiz;                 /* ALT_SDMMC_BLKSIZ */
    volatile uint32_t  bytcnt;                 /* ALT_SDMMC_BYTCNT */
    volatile uint32_t  intmask;                /* ALT_SDMMC_INTMSK */
    volatile uint32_t  cmdarg;                 /* ALT_SDMMC_CMDARG */
    volatile uint32_t  cmd;                    /* ALT_SDMMC_CMD */
    volatile uint32_t  resp0;                  /* ALT_SDMMC_RESP0 */
    volatile uint32_t  resp1;                  /* ALT_SDMMC_RESP1 */
    volatile uint32_t  resp2;                  /* ALT_SDMMC_RESP2 */
    volatile uint32_t  resp3;                  /* ALT_SDMMC_RESP3 */
    volatile uint32_t  mintsts;                /* ALT_SDMMC_MINTSTS */
    volatile uint32_t  rintsts;                /* ALT_SDMMC_RINTSTS */
    volatile uint32_t  status;                 /* ALT_SDMMC_STAT */
    volatile uint32_t  fifoth;                 /* ALT_SDMMC_FIFOTH */
    volatile uint32_t  cdetect;                /* ALT_SDMMC_CDETECT */
    volatile uint32_t  wrtprt;                 /* ALT_SDMMC_WRTPRT */
    volatile uint32_t  _pad_0x58_0x5b;         /* *UNDEFINED* */
    volatile uint32_t  tcbcnt;                 /* ALT_SDMMC_TCBCNT */
    volatile uint32_t  tbbcnt;                 /* ALT_SDMMC_TBBCNT */
    volatile uint32_t  debnce;                 /* ALT_SDMMC_DEBNCE */
    volatile uint32_t  usrid;                  /* ALT_SDMMC_USRID */
    volatile uint32_t  verid;                  /* ALT_SDMMC_VERID */
    volatile uint32_t  hcon;                   /* ALT_SDMMC_HCON */
    volatile uint32_t  uhs_reg;                /* ALT_SDMMC_UHS_REG */
    volatile uint32_t  rst_n;                  /* ALT_SDMMC_RST_N */
    volatile uint32_t  _pad_0x7c_0x7f;         /* *UNDEFINED* */
    volatile uint32_t  bmod;                   /* ALT_SDMMC_BMOD */
    volatile uint32_t  pldmnd;                 /* ALT_SDMMC_PLDMND */
    volatile uint32_t  dbaddr;                 /* ALT_SDMMC_DBADDR */
    volatile uint32_t  idsts;                  /* ALT_SDMMC_IDSTS */
    volatile uint32_t  idinten;                /* ALT_SDMMC_IDINTEN */
    volatile uint32_t  dscaddr;                /* ALT_SDMMC_DSCADDR */
    volatile uint32_t  bufaddr;                /* ALT_SDMMC_BUFADDR */
    volatile uint32_t  _pad_0x9c_0xff[25];     /* *UNDEFINED* */
    volatile uint32_t  cardthrctl;             /* ALT_SDMMC_CARDTHRCTL */
    volatile uint32_t  back_end_power_r;       /* ALT_SDMMC_BACK_END_POWER_R */
    volatile uint32_t  _pad_0x108_0x1ff[62];   /* *UNDEFINED* */
    volatile uint32_t  data;                   /* ALT_SDMMC_DATA */
    volatile uint32_t  _pad_0x204_0x400[127];  /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_SDMMC. */
typedef volatile struct ALT_SDMMC_raw_s  ALT_SDMMC_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_SDMMC_H__ */

