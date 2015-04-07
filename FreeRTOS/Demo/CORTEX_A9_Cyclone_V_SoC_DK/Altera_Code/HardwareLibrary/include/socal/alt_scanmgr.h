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

/* Altera - ALT_SCANMGR */

#ifndef __ALTERA_ALT_SCANMGR_H__
#define __ALTERA_ALT_SCANMGR_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : Scan Manager Module Registers - ALT_SCANMGR
 * Scan Manager Module Registers
 * 
 * Registers in the Scan Manager module.
 * 
 * These registers are implemented by an ARM JTAG-AP module from the ARM DAP. Some
 * register and field names have been changed to match the usage in the Scan
 * Manager. If modified, the corresponding names from the ARM documentation are
 * provided. Only registers and fields that are relevant to the JTAG-AP use in the
 * Scan Manager are listed.
 * 
 */
/*
 * Register : Control/Status Word Register - stat
 * 
 * Consist of control bit and status information.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                         
 * :--------|:-------|:--------|:-------------------------------------
 *  [0]     | ???    | 0x0     | *UNDEFINED*                         
 *  [1]     | RW     | 0x0     | Reset output to the FPGA JTAG       
 *  [2]     | ???    | 0x0     | *UNDEFINED*                         
 *  [3]     | R      | Unknown | Ignore                              
 *  [23:4]  | ???    | 0x0     | *UNDEFINED*                         
 *  [26:24] | R      | 0x0     | Response FIFO Outstanding Byte Count
 *  [27]    | ???    | 0x0     | *UNDEFINED*                         
 *  [30:28] | R      | 0x0     | Command FIFO Outstanding Byte Count 
 *  [31]    | R      | 0x0     | Scan-Chain Engine Active            
 * 
 */
/*
 * Field : Reset output to the FPGA JTAG - trst
 * 
 * Specifies the value of the nTRST signal driven to the FPGA JTAG only. The FPGA
 * JTAG scan-chain must be enabled via the EN register to drive the value specified
 * in this field. The nTRST signal is driven with the inverted value of this
 * field.The nTRST signal is active low so, when this bit is set to 1, FPGA JTAG is
 * reset.
 * 
 * The name of this field in ARM documentation is TRST_OUT.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                       | Value | Description                                     
 * :-------------------------------------------|:------|:-------------------------------------------------
 *  ALT_SCANMGR_STAT_TRST_E_DONT_RST_FPGA_JTAG | 0x0   | Don't reset FPGA JTAG.                          
 *  ALT_SCANMGR_STAT_TRST_E_RST_FPGA_JTAG      | 0x1   | Reset FPGA JTAG. Must have the FPGA JTAG scan-  
 * :                                           |       | chain enabled in the EN register to take effect.
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SCANMGR_STAT_TRST
 * 
 * Don't reset FPGA JTAG.
 */
#define ALT_SCANMGR_STAT_TRST_E_DONT_RST_FPGA_JTAG  0x0
/*
 * Enumerated value for register field ALT_SCANMGR_STAT_TRST
 * 
 * Reset FPGA JTAG. Must have the FPGA JTAG scan-chain enabled in the EN register
 * to take effect.
 */
#define ALT_SCANMGR_STAT_TRST_E_RST_FPGA_JTAG       0x1

/* The Least Significant Bit (LSB) position of the ALT_SCANMGR_STAT_TRST register field. */
#define ALT_SCANMGR_STAT_TRST_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SCANMGR_STAT_TRST register field. */
#define ALT_SCANMGR_STAT_TRST_MSB        1
/* The width in bits of the ALT_SCANMGR_STAT_TRST register field. */
#define ALT_SCANMGR_STAT_TRST_WIDTH      1
/* The mask used to set the ALT_SCANMGR_STAT_TRST register field value. */
#define ALT_SCANMGR_STAT_TRST_SET_MSK    0x00000002
/* The mask used to clear the ALT_SCANMGR_STAT_TRST register field value. */
#define ALT_SCANMGR_STAT_TRST_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SCANMGR_STAT_TRST register field. */
#define ALT_SCANMGR_STAT_TRST_RESET      0x0
/* Extracts the ALT_SCANMGR_STAT_TRST field value from a register. */
#define ALT_SCANMGR_STAT_TRST_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SCANMGR_STAT_TRST register field value suitable for setting the register. */
#define ALT_SCANMGR_STAT_TRST_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Ignore - ignore
 * 
 * Ignore this field. Its value is undefined (may be 0 or 1).
 * 
 * The name of this field in ARM documentation is PORTCONNECTED.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SCANMGR_STAT_IGNORE register field. */
#define ALT_SCANMGR_STAT_IGNORE_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SCANMGR_STAT_IGNORE register field. */
#define ALT_SCANMGR_STAT_IGNORE_MSB        3
/* The width in bits of the ALT_SCANMGR_STAT_IGNORE register field. */
#define ALT_SCANMGR_STAT_IGNORE_WIDTH      1
/* The mask used to set the ALT_SCANMGR_STAT_IGNORE register field value. */
#define ALT_SCANMGR_STAT_IGNORE_SET_MSK    0x00000008
/* The mask used to clear the ALT_SCANMGR_STAT_IGNORE register field value. */
#define ALT_SCANMGR_STAT_IGNORE_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SCANMGR_STAT_IGNORE register field is UNKNOWN. */
#define ALT_SCANMGR_STAT_IGNORE_RESET      0x0
/* Extracts the ALT_SCANMGR_STAT_IGNORE field value from a register. */
#define ALT_SCANMGR_STAT_IGNORE_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SCANMGR_STAT_IGNORE register field value suitable for setting the register. */
#define ALT_SCANMGR_STAT_IGNORE_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Response FIFO Outstanding Byte Count - rfifocnt
 * 
 * Response FIFO outstanding byte count. Returns the number of bytes of response
 * data available in the Response FIFO.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SCANMGR_STAT_RFIFOCNT register field. */
#define ALT_SCANMGR_STAT_RFIFOCNT_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_SCANMGR_STAT_RFIFOCNT register field. */
#define ALT_SCANMGR_STAT_RFIFOCNT_MSB        26
/* The width in bits of the ALT_SCANMGR_STAT_RFIFOCNT register field. */
#define ALT_SCANMGR_STAT_RFIFOCNT_WIDTH      3
/* The mask used to set the ALT_SCANMGR_STAT_RFIFOCNT register field value. */
#define ALT_SCANMGR_STAT_RFIFOCNT_SET_MSK    0x07000000
/* The mask used to clear the ALT_SCANMGR_STAT_RFIFOCNT register field value. */
#define ALT_SCANMGR_STAT_RFIFOCNT_CLR_MSK    0xf8ffffff
/* The reset value of the ALT_SCANMGR_STAT_RFIFOCNT register field. */
#define ALT_SCANMGR_STAT_RFIFOCNT_RESET      0x0
/* Extracts the ALT_SCANMGR_STAT_RFIFOCNT field value from a register. */
#define ALT_SCANMGR_STAT_RFIFOCNT_GET(value) (((value) & 0x07000000) >> 24)
/* Produces a ALT_SCANMGR_STAT_RFIFOCNT register field value suitable for setting the register. */
#define ALT_SCANMGR_STAT_RFIFOCNT_SET(value) (((value) << 24) & 0x07000000)

/*
 * Field : Command FIFO Outstanding Byte Count - wfifocnt
 * 
 * Command FIFO outstanding byte count. Returns the number of command bytes held in
 * the Command FIFO that have yet to be processed by the Scan-Chain Engine.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SCANMGR_STAT_WFIFOCNT register field. */
#define ALT_SCANMGR_STAT_WFIFOCNT_LSB        28
/* The Most Significant Bit (MSB) position of the ALT_SCANMGR_STAT_WFIFOCNT register field. */
#define ALT_SCANMGR_STAT_WFIFOCNT_MSB        30
/* The width in bits of the ALT_SCANMGR_STAT_WFIFOCNT register field. */
#define ALT_SCANMGR_STAT_WFIFOCNT_WIDTH      3
/* The mask used to set the ALT_SCANMGR_STAT_WFIFOCNT register field value. */
#define ALT_SCANMGR_STAT_WFIFOCNT_SET_MSK    0x70000000
/* The mask used to clear the ALT_SCANMGR_STAT_WFIFOCNT register field value. */
#define ALT_SCANMGR_STAT_WFIFOCNT_CLR_MSK    0x8fffffff
/* The reset value of the ALT_SCANMGR_STAT_WFIFOCNT register field. */
#define ALT_SCANMGR_STAT_WFIFOCNT_RESET      0x0
/* Extracts the ALT_SCANMGR_STAT_WFIFOCNT field value from a register. */
#define ALT_SCANMGR_STAT_WFIFOCNT_GET(value) (((value) & 0x70000000) >> 28)
/* Produces a ALT_SCANMGR_STAT_WFIFOCNT register field value suitable for setting the register. */
#define ALT_SCANMGR_STAT_WFIFOCNT_SET(value) (((value) << 28) & 0x70000000)

/*
 * Field : Scan-Chain Engine Active - active
 * 
 * Indicates if the Scan-Chain Engine is processing commands from the Command FIFO
 * or not.
 * 
 * The Scan-Chain Engine is only guaranteed to be inactive if both the ACTIVE and
 * WFIFOCNT fields are zero.
 * 
 * The name of this field in ARM documentation is SERACTV.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description                                   
 * :--------------------------------------|:------|:-----------------------------------------------
 *  ALT_SCANMGR_STAT_ACT_E_POSSIBLY_INACT | 0x0   | The Scan-Chain Engine may or may not be       
 * :                                      |       | processing commands from the Command FIFO. The
 * :                                      |       | Scan-Chain Engine is only guaranteed to be    
 * :                                      |       | inactive if both this ACTIVE field and the    
 * :                                      |       | WFIFOCNT fields are both zero.                
 *  ALT_SCANMGR_STAT_ACT_E_ACT            | 0x1   | The Scan-Chain Engine is processing commands  
 * :                                      |       | from the Command FIFO.                        
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SCANMGR_STAT_ACT
 * 
 * The Scan-Chain Engine may or may not be processing commands from the Command
 * FIFO. The Scan-Chain Engine is only guaranteed to be inactive if both this
 * ACTIVE field and the WFIFOCNT fields are both zero.
 */
#define ALT_SCANMGR_STAT_ACT_E_POSSIBLY_INACT   0x0
/*
 * Enumerated value for register field ALT_SCANMGR_STAT_ACT
 * 
 * The Scan-Chain Engine is processing commands from the Command FIFO.
 */
#define ALT_SCANMGR_STAT_ACT_E_ACT              0x1

/* The Least Significant Bit (LSB) position of the ALT_SCANMGR_STAT_ACT register field. */
#define ALT_SCANMGR_STAT_ACT_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_SCANMGR_STAT_ACT register field. */
#define ALT_SCANMGR_STAT_ACT_MSB        31
/* The width in bits of the ALT_SCANMGR_STAT_ACT register field. */
#define ALT_SCANMGR_STAT_ACT_WIDTH      1
/* The mask used to set the ALT_SCANMGR_STAT_ACT register field value. */
#define ALT_SCANMGR_STAT_ACT_SET_MSK    0x80000000
/* The mask used to clear the ALT_SCANMGR_STAT_ACT register field value. */
#define ALT_SCANMGR_STAT_ACT_CLR_MSK    0x7fffffff
/* The reset value of the ALT_SCANMGR_STAT_ACT register field. */
#define ALT_SCANMGR_STAT_ACT_RESET      0x0
/* Extracts the ALT_SCANMGR_STAT_ACT field value from a register. */
#define ALT_SCANMGR_STAT_ACT_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_SCANMGR_STAT_ACT register field value suitable for setting the register. */
#define ALT_SCANMGR_STAT_ACT_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SCANMGR_STAT.
 */
struct ALT_SCANMGR_STAT_s
{
    uint32_t                 :  1;  /* *UNDEFINED* */
    uint32_t        trst     :  1;  /* Reset output to the FPGA JTAG */
    uint32_t                 :  1;  /* *UNDEFINED* */
    const uint32_t  ignore   :  1;  /* Ignore */
    uint32_t                 : 20;  /* *UNDEFINED* */
    const uint32_t  rfifocnt :  3;  /* Response FIFO Outstanding Byte Count */
    uint32_t                 :  1;  /* *UNDEFINED* */
    const uint32_t  wfifocnt :  3;  /* Command FIFO Outstanding Byte Count */
    const uint32_t  active   :  1;  /* Scan-Chain Engine Active */
};

/* The typedef declaration for register ALT_SCANMGR_STAT. */
typedef volatile struct ALT_SCANMGR_STAT_s  ALT_SCANMGR_STAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SCANMGR_STAT register from the beginning of the component. */
#define ALT_SCANMGR_STAT_OFST        0x0

/*
 * Register : Scan-Chain Enable Register - en
 * 
 * This register is used to enable one of the 5 scan-chains (0-3 and 7). Only one
 * scan-chain must be enabled at a time. A scan-chain is enabled by writing its
 * corresponding enable field.
 * 
 * Software must use the System Manager to put the corresponding I/O scan-chain
 * into the frozen state before attempting to send I/O configuration data to the
 * I/O scan-chain.
 * 
 * Software must only write to this register when the Scan-Chain Engine is
 * inactive.Writing this field at any other time has unpredictable results. This
 * means that before writing to this field, software must read the STAT register
 * and check that the ACTIVE and WFIFOCNT fields are both zero.
 * 
 * The name of this register in ARM documentation is PSEL.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                
 * :-------|:-------|:------|:----------------------------
 *  [0]    | RW     | 0x0   | I/O Scan-Chain 0 Enable    
 *  [1]    | RW     | 0x0   | I/O Scan-Chain 1 Enable    
 *  [2]    | RW     | 0x0   | I/O Scan-Chain 2 Enable    
 *  [3]    | RW     | 0x0   | I/O Scan-Chain 3 Enable    
 *  [6:4]  | ???    | 0x0   | *UNDEFINED*                
 *  [7]    | RW     | 0x0   | FPGA JTAG Scan-Chain Enable
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                
 * 
 */
/*
 * Field : I/O Scan-Chain 0 Enable - ioscanchain0
 * 
 * Used to enable or disable I/O Scan-Chain 0
 * 
 * The name of this field in ARM documentation is PSEL0.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description       
 * :----------------------------------|:------|:-------------------
 *  ALT_SCANMGR_EN_IOSCANCHAIN0_E_DIS | 0x0   | Disable scan-chain
 *  ALT_SCANMGR_EN_IOSCANCHAIN0_E_EN  | 0x1   | Enable scan-chain 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SCANMGR_EN_IOSCANCHAIN0
 * 
 * Disable scan-chain
 */
#define ALT_SCANMGR_EN_IOSCANCHAIN0_E_DIS   0x0
/*
 * Enumerated value for register field ALT_SCANMGR_EN_IOSCANCHAIN0
 * 
 * Enable scan-chain
 */
#define ALT_SCANMGR_EN_IOSCANCHAIN0_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_SCANMGR_EN_IOSCANCHAIN0 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SCANMGR_EN_IOSCANCHAIN0 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN0_MSB        0
/* The width in bits of the ALT_SCANMGR_EN_IOSCANCHAIN0 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN0_WIDTH      1
/* The mask used to set the ALT_SCANMGR_EN_IOSCANCHAIN0 register field value. */
#define ALT_SCANMGR_EN_IOSCANCHAIN0_SET_MSK    0x00000001
/* The mask used to clear the ALT_SCANMGR_EN_IOSCANCHAIN0 register field value. */
#define ALT_SCANMGR_EN_IOSCANCHAIN0_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SCANMGR_EN_IOSCANCHAIN0 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN0_RESET      0x0
/* Extracts the ALT_SCANMGR_EN_IOSCANCHAIN0 field value from a register. */
#define ALT_SCANMGR_EN_IOSCANCHAIN0_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SCANMGR_EN_IOSCANCHAIN0 register field value suitable for setting the register. */
#define ALT_SCANMGR_EN_IOSCANCHAIN0_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : I/O Scan-Chain 1 Enable - ioscanchain1
 * 
 * Used to enable or disable I/O Scan-Chain 1
 * 
 * The name of this field in ARM documentation is PSEL1.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description       
 * :----------------------------------|:------|:-------------------
 *  ALT_SCANMGR_EN_IOSCANCHAIN1_E_DIS | 0x0   | Disable scan-chain
 *  ALT_SCANMGR_EN_IOSCANCHAIN1_E_EN  | 0x1   | Enable scan-chain 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SCANMGR_EN_IOSCANCHAIN1
 * 
 * Disable scan-chain
 */
#define ALT_SCANMGR_EN_IOSCANCHAIN1_E_DIS   0x0
/*
 * Enumerated value for register field ALT_SCANMGR_EN_IOSCANCHAIN1
 * 
 * Enable scan-chain
 */
#define ALT_SCANMGR_EN_IOSCANCHAIN1_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_SCANMGR_EN_IOSCANCHAIN1 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN1_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SCANMGR_EN_IOSCANCHAIN1 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN1_MSB        1
/* The width in bits of the ALT_SCANMGR_EN_IOSCANCHAIN1 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN1_WIDTH      1
/* The mask used to set the ALT_SCANMGR_EN_IOSCANCHAIN1 register field value. */
#define ALT_SCANMGR_EN_IOSCANCHAIN1_SET_MSK    0x00000002
/* The mask used to clear the ALT_SCANMGR_EN_IOSCANCHAIN1 register field value. */
#define ALT_SCANMGR_EN_IOSCANCHAIN1_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SCANMGR_EN_IOSCANCHAIN1 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN1_RESET      0x0
/* Extracts the ALT_SCANMGR_EN_IOSCANCHAIN1 field value from a register. */
#define ALT_SCANMGR_EN_IOSCANCHAIN1_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SCANMGR_EN_IOSCANCHAIN1 register field value suitable for setting the register. */
#define ALT_SCANMGR_EN_IOSCANCHAIN1_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : I/O Scan-Chain 2 Enable - ioscanchain2
 * 
 * Used to enable or disable I/O Scan-Chain 2
 * 
 * The name of this field in ARM documentation is PSEL2.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description       
 * :----------------------------------|:------|:-------------------
 *  ALT_SCANMGR_EN_IOSCANCHAIN2_E_DIS | 0x0   | Disable scan-chain
 *  ALT_SCANMGR_EN_IOSCANCHAIN2_E_EN  | 0x1   | Enable scan-chain 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SCANMGR_EN_IOSCANCHAIN2
 * 
 * Disable scan-chain
 */
#define ALT_SCANMGR_EN_IOSCANCHAIN2_E_DIS   0x0
/*
 * Enumerated value for register field ALT_SCANMGR_EN_IOSCANCHAIN2
 * 
 * Enable scan-chain
 */
#define ALT_SCANMGR_EN_IOSCANCHAIN2_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_SCANMGR_EN_IOSCANCHAIN2 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN2_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SCANMGR_EN_IOSCANCHAIN2 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN2_MSB        2
/* The width in bits of the ALT_SCANMGR_EN_IOSCANCHAIN2 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN2_WIDTH      1
/* The mask used to set the ALT_SCANMGR_EN_IOSCANCHAIN2 register field value. */
#define ALT_SCANMGR_EN_IOSCANCHAIN2_SET_MSK    0x00000004
/* The mask used to clear the ALT_SCANMGR_EN_IOSCANCHAIN2 register field value. */
#define ALT_SCANMGR_EN_IOSCANCHAIN2_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SCANMGR_EN_IOSCANCHAIN2 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN2_RESET      0x0
/* Extracts the ALT_SCANMGR_EN_IOSCANCHAIN2 field value from a register. */
#define ALT_SCANMGR_EN_IOSCANCHAIN2_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SCANMGR_EN_IOSCANCHAIN2 register field value suitable for setting the register. */
#define ALT_SCANMGR_EN_IOSCANCHAIN2_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : I/O Scan-Chain 3 Enable - ioscanchain3
 * 
 * Used to enable or disable I/O Scan-Chain 3
 * 
 * The name of this field in ARM documentation is PSEL3.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description       
 * :----------------------------------|:------|:-------------------
 *  ALT_SCANMGR_EN_IOSCANCHAIN3_E_DIS | 0x0   | Disable scan-chain
 *  ALT_SCANMGR_EN_IOSCANCHAIN3_E_EN  | 0x1   | Enable scan-chain 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SCANMGR_EN_IOSCANCHAIN3
 * 
 * Disable scan-chain
 */
#define ALT_SCANMGR_EN_IOSCANCHAIN3_E_DIS   0x0
/*
 * Enumerated value for register field ALT_SCANMGR_EN_IOSCANCHAIN3
 * 
 * Enable scan-chain
 */
#define ALT_SCANMGR_EN_IOSCANCHAIN3_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_SCANMGR_EN_IOSCANCHAIN3 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN3_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SCANMGR_EN_IOSCANCHAIN3 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN3_MSB        3
/* The width in bits of the ALT_SCANMGR_EN_IOSCANCHAIN3 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN3_WIDTH      1
/* The mask used to set the ALT_SCANMGR_EN_IOSCANCHAIN3 register field value. */
#define ALT_SCANMGR_EN_IOSCANCHAIN3_SET_MSK    0x00000008
/* The mask used to clear the ALT_SCANMGR_EN_IOSCANCHAIN3 register field value. */
#define ALT_SCANMGR_EN_IOSCANCHAIN3_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SCANMGR_EN_IOSCANCHAIN3 register field. */
#define ALT_SCANMGR_EN_IOSCANCHAIN3_RESET      0x0
/* Extracts the ALT_SCANMGR_EN_IOSCANCHAIN3 field value from a register. */
#define ALT_SCANMGR_EN_IOSCANCHAIN3_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SCANMGR_EN_IOSCANCHAIN3 register field value suitable for setting the register. */
#define ALT_SCANMGR_EN_IOSCANCHAIN3_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : FPGA JTAG Scan-Chain Enable - fpgajtag
 * 
 * Used to enable or disable FPGA JTAG scan-chain.Software must use the System
 * Manager to enable the Scan Manager to drive the FPGA JTAG before attempting to
 * communicate with the FPGA JTAG via the Scan Manager.
 * 
 * The name of this field in ARM documentation is PSEL7.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description       
 * :------------------------------|:------|:-------------------
 *  ALT_SCANMGR_EN_FPGAJTAG_E_DIS | 0x0   | Disable scan-chain
 *  ALT_SCANMGR_EN_FPGAJTAG_E_EN  | 0x1   | Enable scan-chain 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_SCANMGR_EN_FPGAJTAG
 * 
 * Disable scan-chain
 */
#define ALT_SCANMGR_EN_FPGAJTAG_E_DIS   0x0
/*
 * Enumerated value for register field ALT_SCANMGR_EN_FPGAJTAG
 * 
 * Enable scan-chain
 */
#define ALT_SCANMGR_EN_FPGAJTAG_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_SCANMGR_EN_FPGAJTAG register field. */
#define ALT_SCANMGR_EN_FPGAJTAG_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_SCANMGR_EN_FPGAJTAG register field. */
#define ALT_SCANMGR_EN_FPGAJTAG_MSB        7
/* The width in bits of the ALT_SCANMGR_EN_FPGAJTAG register field. */
#define ALT_SCANMGR_EN_FPGAJTAG_WIDTH      1
/* The mask used to set the ALT_SCANMGR_EN_FPGAJTAG register field value. */
#define ALT_SCANMGR_EN_FPGAJTAG_SET_MSK    0x00000080
/* The mask used to clear the ALT_SCANMGR_EN_FPGAJTAG register field value. */
#define ALT_SCANMGR_EN_FPGAJTAG_CLR_MSK    0xffffff7f
/* The reset value of the ALT_SCANMGR_EN_FPGAJTAG register field. */
#define ALT_SCANMGR_EN_FPGAJTAG_RESET      0x0
/* Extracts the ALT_SCANMGR_EN_FPGAJTAG field value from a register. */
#define ALT_SCANMGR_EN_FPGAJTAG_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_SCANMGR_EN_FPGAJTAG register field value suitable for setting the register. */
#define ALT_SCANMGR_EN_FPGAJTAG_SET(value) (((value) << 7) & 0x00000080)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SCANMGR_EN.
 */
struct ALT_SCANMGR_EN_s
{
    uint32_t  ioscanchain0 :  1;  /* I/O Scan-Chain 0 Enable */
    uint32_t  ioscanchain1 :  1;  /* I/O Scan-Chain 1 Enable */
    uint32_t  ioscanchain2 :  1;  /* I/O Scan-Chain 2 Enable */
    uint32_t  ioscanchain3 :  1;  /* I/O Scan-Chain 3 Enable */
    uint32_t               :  3;  /* *UNDEFINED* */
    uint32_t  fpgajtag     :  1;  /* FPGA JTAG Scan-Chain Enable */
    uint32_t               : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SCANMGR_EN. */
typedef volatile struct ALT_SCANMGR_EN_s  ALT_SCANMGR_EN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SCANMGR_EN register from the beginning of the component. */
#define ALT_SCANMGR_EN_OFST        0x4

/*
 * Register : FIFO Single Byte Register - fifosinglebyte
 * 
 * Writes to the FIFO Single Byte Register write a single byte value to the command
 * FIFO.  If the command FIFO is full, the APB write operation is stalled until the
 * command FIFO is not full.
 * 
 * Reads from the Single Byte FIFO Register read a single byte value from the
 * command FIFO.  If the command FIFO is empty, the APB read operation is stalled
 * until the command FIFO is not empty.
 * 
 * See the ARM documentation for a description of the read and write values.
 * 
 * The name of this register in ARM documentation is BWFIFO1 for writes and BRFIFO1
 * for reads.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description      
 * :-------|:-------|:--------|:------------------
 *  [7:0]  | RW     | Unknown | Single Byte Value
 *  [31:8] | ???    | 0x0     | *UNDEFINED*      
 * 
 */
/*
 * Field : Single Byte Value - value
 * 
 * Transfers single byte value to/from command FIFO
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SCANMGR_FIFOSINGLEBYTE_VALUE register field. */
#define ALT_SCANMGR_FIFOSINGLEBYTE_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SCANMGR_FIFOSINGLEBYTE_VALUE register field. */
#define ALT_SCANMGR_FIFOSINGLEBYTE_VALUE_MSB        7
/* The width in bits of the ALT_SCANMGR_FIFOSINGLEBYTE_VALUE register field. */
#define ALT_SCANMGR_FIFOSINGLEBYTE_VALUE_WIDTH      8
/* The mask used to set the ALT_SCANMGR_FIFOSINGLEBYTE_VALUE register field value. */
#define ALT_SCANMGR_FIFOSINGLEBYTE_VALUE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SCANMGR_FIFOSINGLEBYTE_VALUE register field value. */
#define ALT_SCANMGR_FIFOSINGLEBYTE_VALUE_CLR_MSK    0xffffff00
/* The reset value of the ALT_SCANMGR_FIFOSINGLEBYTE_VALUE register field is UNKNOWN. */
#define ALT_SCANMGR_FIFOSINGLEBYTE_VALUE_RESET      0x0
/* Extracts the ALT_SCANMGR_FIFOSINGLEBYTE_VALUE field value from a register. */
#define ALT_SCANMGR_FIFOSINGLEBYTE_VALUE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SCANMGR_FIFOSINGLEBYTE_VALUE register field value suitable for setting the register. */
#define ALT_SCANMGR_FIFOSINGLEBYTE_VALUE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SCANMGR_FIFOSINGLEBYTE.
 */
struct ALT_SCANMGR_FIFOSINGLEBYTE_s
{
    uint32_t  value :  8;  /* Single Byte Value */
    uint32_t        : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SCANMGR_FIFOSINGLEBYTE. */
typedef volatile struct ALT_SCANMGR_FIFOSINGLEBYTE_s  ALT_SCANMGR_FIFOSINGLEBYTE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SCANMGR_FIFOSINGLEBYTE register from the beginning of the component. */
#define ALT_SCANMGR_FIFOSINGLEBYTE_OFST        0x10

/*
 * Register : FIFO Double Byte Register - fifodoublebyte
 * 
 * Writes to the FIFO Double Byte Register write a double byte value to the command
 * FIFO.  If the command FIFO is full, the APB write operation is stalled until the
 * command FIFO is not full.
 * 
 * Reads from the Double Byte FIFO Register read a double byte value from the
 * command FIFO.  If the command FIFO is empty, the APB read operation is stalled
 * until the command FIFO is not empty.
 * 
 * See the ARM documentation for a description of the read and write values.
 * 
 * The name of this register in ARM documentation is BWFIFO2 for writes and BRFIFO2
 * for reads.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description      
 * :--------|:-------|:--------|:------------------
 *  [15:0]  | RW     | Unknown | Double Byte Value
 *  [31:16] | ???    | 0x0     | *UNDEFINED*      
 * 
 */
/*
 * Field : Double Byte Value - value
 * 
 * Transfers double byte value to/from command FIFO
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SCANMGR_FIFODOUBLEBYTE_VALUE register field. */
#define ALT_SCANMGR_FIFODOUBLEBYTE_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SCANMGR_FIFODOUBLEBYTE_VALUE register field. */
#define ALT_SCANMGR_FIFODOUBLEBYTE_VALUE_MSB        15
/* The width in bits of the ALT_SCANMGR_FIFODOUBLEBYTE_VALUE register field. */
#define ALT_SCANMGR_FIFODOUBLEBYTE_VALUE_WIDTH      16
/* The mask used to set the ALT_SCANMGR_FIFODOUBLEBYTE_VALUE register field value. */
#define ALT_SCANMGR_FIFODOUBLEBYTE_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_SCANMGR_FIFODOUBLEBYTE_VALUE register field value. */
#define ALT_SCANMGR_FIFODOUBLEBYTE_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_SCANMGR_FIFODOUBLEBYTE_VALUE register field is UNKNOWN. */
#define ALT_SCANMGR_FIFODOUBLEBYTE_VALUE_RESET      0x0
/* Extracts the ALT_SCANMGR_FIFODOUBLEBYTE_VALUE field value from a register. */
#define ALT_SCANMGR_FIFODOUBLEBYTE_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_SCANMGR_FIFODOUBLEBYTE_VALUE register field value suitable for setting the register. */
#define ALT_SCANMGR_FIFODOUBLEBYTE_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SCANMGR_FIFODOUBLEBYTE.
 */
struct ALT_SCANMGR_FIFODOUBLEBYTE_s
{
    uint32_t  value : 16;  /* Double Byte Value */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SCANMGR_FIFODOUBLEBYTE. */
typedef volatile struct ALT_SCANMGR_FIFODOUBLEBYTE_s  ALT_SCANMGR_FIFODOUBLEBYTE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SCANMGR_FIFODOUBLEBYTE register from the beginning of the component. */
#define ALT_SCANMGR_FIFODOUBLEBYTE_OFST        0x14

/*
 * Register : FIFO Triple Byte Register - fifotriplebyte
 * 
 * Writes to the FIFO Triple Byte Register write a triple byte value to the command
 * FIFO.  If the command FIFO is full, the APB write operation is stalled until the
 * command FIFO is not full.
 * 
 * Reads from the Triple Byte FIFO Register read a triple byte value from the
 * command FIFO.  If the command FIFO is empty, the APB read operation is stalled
 * until the command FIFO is not empty.
 * 
 * See the ARM documentation for a description of the read and write values.
 * 
 * The name of this register in ARM documentation is BWFIFO3 for writes and BRFIFO3
 * for reads.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description      
 * :--------|:-------|:--------|:------------------
 *  [23:0]  | RW     | Unknown | Triple Byte Value
 *  [31:24] | ???    | 0x0     | *UNDEFINED*      
 * 
 */
/*
 * Field : Triple Byte Value - value
 * 
 * Transfers triple byte value to/from command FIFO
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE register field. */
#define ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE register field. */
#define ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE_MSB        23
/* The width in bits of the ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE register field. */
#define ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE_WIDTH      24
/* The mask used to set the ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE register field value. */
#define ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE_SET_MSK    0x00ffffff
/* The mask used to clear the ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE register field value. */
#define ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE_CLR_MSK    0xff000000
/* The reset value of the ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE register field is UNKNOWN. */
#define ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE_RESET      0x0
/* Extracts the ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE field value from a register. */
#define ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE_GET(value) (((value) & 0x00ffffff) >> 0)
/* Produces a ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE register field value suitable for setting the register. */
#define ALT_SCANMGR_FIFOTRIPLEBYTE_VALUE_SET(value) (((value) << 0) & 0x00ffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SCANMGR_FIFOTRIPLEBYTE.
 */
struct ALT_SCANMGR_FIFOTRIPLEBYTE_s
{
    uint32_t  value : 24;  /* Triple Byte Value */
    uint32_t        :  8;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SCANMGR_FIFOTRIPLEBYTE. */
typedef volatile struct ALT_SCANMGR_FIFOTRIPLEBYTE_s  ALT_SCANMGR_FIFOTRIPLEBYTE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SCANMGR_FIFOTRIPLEBYTE register from the beginning of the component. */
#define ALT_SCANMGR_FIFOTRIPLEBYTE_OFST        0x18

/*
 * Register : FIFO Quad Byte Register - fifoquadbyte
 * 
 * Writes to the FIFO Quad Byte Register write a quad byte value to the command
 * FIFO.  If the command FIFO is full, the APB write operation is stalled until the
 * command FIFO is not full.
 * 
 * Reads from the Quad Byte FIFO Register read a quad byte value from the command
 * FIFO.  If the command FIFO is empty, the APB read operation is stalled until the
 * command FIFO is not empty.
 * 
 * See the ARM documentation for a description of the read and write values.
 * 
 * The name of this register in ARM documentation is BWFIFO4 for writes and BRFIFO4
 * for reads.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description    
 * :-------|:-------|:--------|:----------------
 *  [31:0] | RW     | Unknown | Quad Byte Value
 * 
 */
/*
 * Field : Quad Byte Value - value
 * 
 * Transfers quad byte value to/from command FIFO
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SCANMGR_FIFOQUADBYTE_VALUE register field. */
#define ALT_SCANMGR_FIFOQUADBYTE_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SCANMGR_FIFOQUADBYTE_VALUE register field. */
#define ALT_SCANMGR_FIFOQUADBYTE_VALUE_MSB        31
/* The width in bits of the ALT_SCANMGR_FIFOQUADBYTE_VALUE register field. */
#define ALT_SCANMGR_FIFOQUADBYTE_VALUE_WIDTH      32
/* The mask used to set the ALT_SCANMGR_FIFOQUADBYTE_VALUE register field value. */
#define ALT_SCANMGR_FIFOQUADBYTE_VALUE_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SCANMGR_FIFOQUADBYTE_VALUE register field value. */
#define ALT_SCANMGR_FIFOQUADBYTE_VALUE_CLR_MSK    0x00000000
/* The reset value of the ALT_SCANMGR_FIFOQUADBYTE_VALUE register field is UNKNOWN. */
#define ALT_SCANMGR_FIFOQUADBYTE_VALUE_RESET      0x0
/* Extracts the ALT_SCANMGR_FIFOQUADBYTE_VALUE field value from a register. */
#define ALT_SCANMGR_FIFOQUADBYTE_VALUE_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SCANMGR_FIFOQUADBYTE_VALUE register field value suitable for setting the register. */
#define ALT_SCANMGR_FIFOQUADBYTE_VALUE_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SCANMGR_FIFOQUADBYTE.
 */
struct ALT_SCANMGR_FIFOQUADBYTE_s
{
    uint32_t  value : 32;  /* Quad Byte Value */
};

/* The typedef declaration for register ALT_SCANMGR_FIFOQUADBYTE. */
typedef volatile struct ALT_SCANMGR_FIFOQUADBYTE_s  ALT_SCANMGR_FIFOQUADBYTE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SCANMGR_FIFOQUADBYTE register from the beginning of the component. */
#define ALT_SCANMGR_FIFOQUADBYTE_OFST        0x1c

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_SCANMGR.
 */
struct ALT_SCANMGR_s
{
    volatile ALT_SCANMGR_STAT_t            stat;             /* ALT_SCANMGR_STAT */
    volatile ALT_SCANMGR_EN_t              en;               /* ALT_SCANMGR_EN */
    volatile uint32_t                      _pad_0x8_0xf[2];  /* *UNDEFINED* */
    volatile ALT_SCANMGR_FIFOSINGLEBYTE_t  fifosinglebyte;   /* ALT_SCANMGR_FIFOSINGLEBYTE */
    volatile ALT_SCANMGR_FIFODOUBLEBYTE_t  fifodoublebyte;   /* ALT_SCANMGR_FIFODOUBLEBYTE */
    volatile ALT_SCANMGR_FIFOTRIPLEBYTE_t  fifotriplebyte;   /* ALT_SCANMGR_FIFOTRIPLEBYTE */
    volatile ALT_SCANMGR_FIFOQUADBYTE_t    fifoquadbyte;     /* ALT_SCANMGR_FIFOQUADBYTE */
};

/* The typedef declaration for register group ALT_SCANMGR. */
typedef volatile struct ALT_SCANMGR_s  ALT_SCANMGR_t;
/* The struct declaration for the raw register contents of register group ALT_SCANMGR. */
struct ALT_SCANMGR_raw_s
{
    volatile uint32_t  stat;             /* ALT_SCANMGR_STAT */
    volatile uint32_t  en;               /* ALT_SCANMGR_EN */
    volatile uint32_t  _pad_0x8_0xf[2];  /* *UNDEFINED* */
    volatile uint32_t  fifosinglebyte;   /* ALT_SCANMGR_FIFOSINGLEBYTE */
    volatile uint32_t  fifodoublebyte;   /* ALT_SCANMGR_FIFODOUBLEBYTE */
    volatile uint32_t  fifotriplebyte;   /* ALT_SCANMGR_FIFOTRIPLEBYTE */
    volatile uint32_t  fifoquadbyte;     /* ALT_SCANMGR_FIFOQUADBYTE */
};

/* The typedef declaration for the raw register contents of register group ALT_SCANMGR. */
typedef volatile struct ALT_SCANMGR_raw_s  ALT_SCANMGR_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_SCANMGR_H__ */

