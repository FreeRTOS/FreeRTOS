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

/* Altera - ALT_NAND */

#ifndef __ALTERA_ALT_NAND_H__
#define __ALTERA_ALT_NAND_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : NAND Flash Controller Module Registers (AXI Slave) - ALT_NAND
 * NAND Flash Controller Module Registers (AXI Slave)
 * 
 * Registers in the NAND Flash Controller module accessible via its register AXI
 * slave
 * 
 */
/*
 * Register Group : Configuration registers - ALT_NAND_CFG
 * Configuration registers
 * 
 * Common across all types of flash devices, configuration registers setup the
 * basic operating modes of the controller
 * 
 */
/*
 * Register : device_reset
 * 
 * Device reset. Controller sends a RESET command to device. Controller resets bit
 * after sending command to device
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_CFG_DEVICE_RST_BANK0
 *  [1]    | RW     | 0x0   | ALT_NAND_CFG_DEVICE_RST_BANK1
 *  [2]    | RW     | 0x0   | ALT_NAND_CFG_DEVICE_RST_BANK2
 *  [3]    | RW     | 0x0   | ALT_NAND_CFG_DEVICE_RST_BANK3
 *  [31:4] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : bank0
 * 
 * Issues reset to bank 0. Controller resets the bit after reset command is issued
 * to device.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_DEVICE_RST_BANK0 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_DEVICE_RST_BANK0 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK0_MSB        0
/* The width in bits of the ALT_NAND_CFG_DEVICE_RST_BANK0 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK0_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_DEVICE_RST_BANK0 register field value. */
#define ALT_NAND_CFG_DEVICE_RST_BANK0_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_DEVICE_RST_BANK0 register field value. */
#define ALT_NAND_CFG_DEVICE_RST_BANK0_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_DEVICE_RST_BANK0 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK0_RESET      0x0
/* Extracts the ALT_NAND_CFG_DEVICE_RST_BANK0 field value from a register. */
#define ALT_NAND_CFG_DEVICE_RST_BANK0_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_DEVICE_RST_BANK0 register field value suitable for setting the register. */
#define ALT_NAND_CFG_DEVICE_RST_BANK0_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : bank1
 * 
 * Issues reset to bank 1. Controller resets the bit after reset command is issued
 * to device.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_DEVICE_RST_BANK1 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK1_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_DEVICE_RST_BANK1 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK1_MSB        1
/* The width in bits of the ALT_NAND_CFG_DEVICE_RST_BANK1 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK1_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_DEVICE_RST_BANK1 register field value. */
#define ALT_NAND_CFG_DEVICE_RST_BANK1_SET_MSK    0x00000002
/* The mask used to clear the ALT_NAND_CFG_DEVICE_RST_BANK1 register field value. */
#define ALT_NAND_CFG_DEVICE_RST_BANK1_CLR_MSK    0xfffffffd
/* The reset value of the ALT_NAND_CFG_DEVICE_RST_BANK1 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK1_RESET      0x0
/* Extracts the ALT_NAND_CFG_DEVICE_RST_BANK1 field value from a register. */
#define ALT_NAND_CFG_DEVICE_RST_BANK1_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_NAND_CFG_DEVICE_RST_BANK1 register field value suitable for setting the register. */
#define ALT_NAND_CFG_DEVICE_RST_BANK1_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : bank2
 * 
 * Issues reset to bank 2. Controller resets the bit after reset command is issued
 * to device.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_DEVICE_RST_BANK2 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK2_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_DEVICE_RST_BANK2 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK2_MSB        2
/* The width in bits of the ALT_NAND_CFG_DEVICE_RST_BANK2 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK2_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_DEVICE_RST_BANK2 register field value. */
#define ALT_NAND_CFG_DEVICE_RST_BANK2_SET_MSK    0x00000004
/* The mask used to clear the ALT_NAND_CFG_DEVICE_RST_BANK2 register field value. */
#define ALT_NAND_CFG_DEVICE_RST_BANK2_CLR_MSK    0xfffffffb
/* The reset value of the ALT_NAND_CFG_DEVICE_RST_BANK2 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK2_RESET      0x0
/* Extracts the ALT_NAND_CFG_DEVICE_RST_BANK2 field value from a register. */
#define ALT_NAND_CFG_DEVICE_RST_BANK2_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_NAND_CFG_DEVICE_RST_BANK2 register field value suitable for setting the register. */
#define ALT_NAND_CFG_DEVICE_RST_BANK2_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : bank3
 * 
 * Issues reset to bank 3. Controller resets the bit after reset command is issued
 * to device.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_DEVICE_RST_BANK3 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK3_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_DEVICE_RST_BANK3 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK3_MSB        3
/* The width in bits of the ALT_NAND_CFG_DEVICE_RST_BANK3 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK3_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_DEVICE_RST_BANK3 register field value. */
#define ALT_NAND_CFG_DEVICE_RST_BANK3_SET_MSK    0x00000008
/* The mask used to clear the ALT_NAND_CFG_DEVICE_RST_BANK3 register field value. */
#define ALT_NAND_CFG_DEVICE_RST_BANK3_CLR_MSK    0xfffffff7
/* The reset value of the ALT_NAND_CFG_DEVICE_RST_BANK3 register field. */
#define ALT_NAND_CFG_DEVICE_RST_BANK3_RESET      0x0
/* Extracts the ALT_NAND_CFG_DEVICE_RST_BANK3 field value from a register. */
#define ALT_NAND_CFG_DEVICE_RST_BANK3_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_NAND_CFG_DEVICE_RST_BANK3 register field value suitable for setting the register. */
#define ALT_NAND_CFG_DEVICE_RST_BANK3_SET(value) (((value) << 3) & 0x00000008)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_DEVICE_RST.
 */
struct ALT_NAND_CFG_DEVICE_RST_s
{
    uint32_t  bank0 :  1;  /* ALT_NAND_CFG_DEVICE_RST_BANK0 */
    uint32_t  bank1 :  1;  /* ALT_NAND_CFG_DEVICE_RST_BANK1 */
    uint32_t  bank2 :  1;  /* ALT_NAND_CFG_DEVICE_RST_BANK2 */
    uint32_t  bank3 :  1;  /* ALT_NAND_CFG_DEVICE_RST_BANK3 */
    uint32_t        : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_DEVICE_RST. */
typedef volatile struct ALT_NAND_CFG_DEVICE_RST_s  ALT_NAND_CFG_DEVICE_RST_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_DEVICE_RST register from the beginning of the component. */
#define ALT_NAND_CFG_DEVICE_RST_OFST        0x0

/*
 * Register : transfer_spare_reg
 * 
 * Default data transfer mode. (Ignored during Spare only mode)
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                    
 * :-------|:-------|:------|:--------------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_CFG_TFR_SPARE_REG_FLAG
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                    
 * 
 */
/*
 * Field : flag
 * 
 * On all read or write commands through Map 01, if this bit is set, data in spare
 * area of memory will be transfered to host along with main area of data. The main
 * area will be transfered followed by spare area.[list][*]1 - MAIN+SPARE [*]0 -
 * MAIN[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_TFR_SPARE_REG_FLAG register field. */
#define ALT_NAND_CFG_TFR_SPARE_REG_FLAG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_TFR_SPARE_REG_FLAG register field. */
#define ALT_NAND_CFG_TFR_SPARE_REG_FLAG_MSB        0
/* The width in bits of the ALT_NAND_CFG_TFR_SPARE_REG_FLAG register field. */
#define ALT_NAND_CFG_TFR_SPARE_REG_FLAG_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_TFR_SPARE_REG_FLAG register field value. */
#define ALT_NAND_CFG_TFR_SPARE_REG_FLAG_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_TFR_SPARE_REG_FLAG register field value. */
#define ALT_NAND_CFG_TFR_SPARE_REG_FLAG_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_TFR_SPARE_REG_FLAG register field. */
#define ALT_NAND_CFG_TFR_SPARE_REG_FLAG_RESET      0x0
/* Extracts the ALT_NAND_CFG_TFR_SPARE_REG_FLAG field value from a register. */
#define ALT_NAND_CFG_TFR_SPARE_REG_FLAG_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_TFR_SPARE_REG_FLAG register field value suitable for setting the register. */
#define ALT_NAND_CFG_TFR_SPARE_REG_FLAG_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_TFR_SPARE_REG.
 */
struct ALT_NAND_CFG_TFR_SPARE_REG_s
{
    uint32_t  flag :  1;  /* ALT_NAND_CFG_TFR_SPARE_REG_FLAG */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_TFR_SPARE_REG. */
typedef volatile struct ALT_NAND_CFG_TFR_SPARE_REG_s  ALT_NAND_CFG_TFR_SPARE_REG_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_TFR_SPARE_REG register from the beginning of the component. */
#define ALT_NAND_CFG_TFR_SPARE_REG_OFST        0x10

/*
 * Register : load_wait_cnt
 * 
 * Wait count value for Load operation
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                   
 * :--------|:-------|:------|:-------------------------------
 *  [15:0]  | RW     | 0x1f4 | ALT_NAND_CFG_LD_WAIT_CNT_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                   
 * 
 */
/*
 * Field : value
 * 
 * Number of clock cycles after issue of load operation before NAND Flash
 * Controller polls for status. This values is of relevance for status polling mode
 * of operation and has been provided to minimize redundant polling after issuing a
 * command. After a load command, the first polling will happen after this many
 * number of cycles have elapsed and then on polling will happen every
 * int_mon_cyccnt cycles. The default values is equal to the default value of
 * int_mon_cyccnt
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_LD_WAIT_CNT_VALUE register field. */
#define ALT_NAND_CFG_LD_WAIT_CNT_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_LD_WAIT_CNT_VALUE register field. */
#define ALT_NAND_CFG_LD_WAIT_CNT_VALUE_MSB        15
/* The width in bits of the ALT_NAND_CFG_LD_WAIT_CNT_VALUE register field. */
#define ALT_NAND_CFG_LD_WAIT_CNT_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_CFG_LD_WAIT_CNT_VALUE register field value. */
#define ALT_NAND_CFG_LD_WAIT_CNT_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_CFG_LD_WAIT_CNT_VALUE register field value. */
#define ALT_NAND_CFG_LD_WAIT_CNT_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_CFG_LD_WAIT_CNT_VALUE register field. */
#define ALT_NAND_CFG_LD_WAIT_CNT_VALUE_RESET      0x1f4
/* Extracts the ALT_NAND_CFG_LD_WAIT_CNT_VALUE field value from a register. */
#define ALT_NAND_CFG_LD_WAIT_CNT_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_CFG_LD_WAIT_CNT_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_LD_WAIT_CNT_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_LD_WAIT_CNT.
 */
struct ALT_NAND_CFG_LD_WAIT_CNT_s
{
    uint32_t  value : 16;  /* ALT_NAND_CFG_LD_WAIT_CNT_VALUE */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_LD_WAIT_CNT. */
typedef volatile struct ALT_NAND_CFG_LD_WAIT_CNT_s  ALT_NAND_CFG_LD_WAIT_CNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_LD_WAIT_CNT register from the beginning of the component. */
#define ALT_NAND_CFG_LD_WAIT_CNT_OFST        0x20

/*
 * Register : program_wait_cnt
 * 
 * Wait count value for Program operation
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                        
 * :--------|:-------|:------|:------------------------------------
 *  [15:0]  | RW     | 0x1f4 | ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : value
 * 
 * Number of clock cycles after issue of program operation before NAND Flash
 * Controller polls for status. This values is of relevance for status polling mode
 * of operation and has been provided to minimize redundant polling after issuing a
 * command. After a program command, the first polling will happen after this many
 * number of cycles have elapsed and then on polling will happen every
 * int_mon_cyccnt cycles. The default values is equal to the default value of
 * int_mon_cyccnt. The controller internally multiplies the value programmed into
 * this register by 16 to provide a wider range for polling.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE register field. */
#define ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE register field. */
#define ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE_MSB        15
/* The width in bits of the ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE register field. */
#define ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE register field value. */
#define ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE register field value. */
#define ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE register field. */
#define ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE_RESET      0x1f4
/* Extracts the ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE field value from a register. */
#define ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_PROGRAM_WAIT_CNT.
 */
struct ALT_NAND_CFG_PROGRAM_WAIT_CNT_s
{
    uint32_t  value : 16;  /* ALT_NAND_CFG_PROGRAM_WAIT_CNT_VALUE */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_PROGRAM_WAIT_CNT. */
typedef volatile struct ALT_NAND_CFG_PROGRAM_WAIT_CNT_s  ALT_NAND_CFG_PROGRAM_WAIT_CNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_PROGRAM_WAIT_CNT register from the beginning of the component. */
#define ALT_NAND_CFG_PROGRAM_WAIT_CNT_OFST        0x30

/*
 * Register : erase_wait_cnt
 * 
 * Wait count value for Erase operation
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                      
 * :--------|:-------|:------|:----------------------------------
 *  [15:0]  | RW     | 0x1f4 | ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                      
 * 
 */
/*
 * Field : value
 * 
 * Number of clock cycles after issue of erase operation before NAND Flash
 * Controller polls for status. This values is of relevance for status polling mode
 * of operation and has been provided to minimize redundant polling after issuing a
 * command. After a erase command, the first polling will happen after this many
 * number of cycles have elapsed and then on polling will happen every
 * int_mon_cyccnt cycles. The default values is equal to the default value of
 * int_mon_cyccnt. The controller internally multiplies the value programmed into
 * this register by 16 to provide a wider range for polling.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE register field. */
#define ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE register field. */
#define ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE_MSB        15
/* The width in bits of the ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE register field. */
#define ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE register field value. */
#define ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE register field value. */
#define ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE register field. */
#define ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE_RESET      0x1f4
/* Extracts the ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE field value from a register. */
#define ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_ERASE_WAIT_CNT.
 */
struct ALT_NAND_CFG_ERASE_WAIT_CNT_s
{
    uint32_t  value : 16;  /* ALT_NAND_CFG_ERASE_WAIT_CNT_VALUE */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_ERASE_WAIT_CNT. */
typedef volatile struct ALT_NAND_CFG_ERASE_WAIT_CNT_s  ALT_NAND_CFG_ERASE_WAIT_CNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_ERASE_WAIT_CNT register from the beginning of the component. */
#define ALT_NAND_CFG_ERASE_WAIT_CNT_OFST        0x40

/*
 * Register : int_mon_cyccnt
 * 
 * Interrupt monitor cycle count value
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                      
 * :--------|:-------|:------|:----------------------------------
 *  [15:0]  | RW     | 0x1f4 | ALT_NAND_CFG_INT_MON_CYCCNT_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                      
 * 
 */
/*
 * Field : value
 * 
 * In polling mode, sets the number of cycles Denali Flash Controller must wait
 * before checking the status register. This register is only used when R/B pins
 * are not available to NAND Flash Controller.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_INT_MON_CYCCNT_VALUE register field. */
#define ALT_NAND_CFG_INT_MON_CYCCNT_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_INT_MON_CYCCNT_VALUE register field. */
#define ALT_NAND_CFG_INT_MON_CYCCNT_VALUE_MSB        15
/* The width in bits of the ALT_NAND_CFG_INT_MON_CYCCNT_VALUE register field. */
#define ALT_NAND_CFG_INT_MON_CYCCNT_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_CFG_INT_MON_CYCCNT_VALUE register field value. */
#define ALT_NAND_CFG_INT_MON_CYCCNT_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_CFG_INT_MON_CYCCNT_VALUE register field value. */
#define ALT_NAND_CFG_INT_MON_CYCCNT_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_CFG_INT_MON_CYCCNT_VALUE register field. */
#define ALT_NAND_CFG_INT_MON_CYCCNT_VALUE_RESET      0x1f4
/* Extracts the ALT_NAND_CFG_INT_MON_CYCCNT_VALUE field value from a register. */
#define ALT_NAND_CFG_INT_MON_CYCCNT_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_CFG_INT_MON_CYCCNT_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_INT_MON_CYCCNT_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_INT_MON_CYCCNT.
 */
struct ALT_NAND_CFG_INT_MON_CYCCNT_s
{
    uint32_t  value : 16;  /* ALT_NAND_CFG_INT_MON_CYCCNT_VALUE */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_INT_MON_CYCCNT. */
typedef volatile struct ALT_NAND_CFG_INT_MON_CYCCNT_s  ALT_NAND_CFG_INT_MON_CYCCNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_INT_MON_CYCCNT register from the beginning of the component. */
#define ALT_NAND_CFG_INT_MON_CYCCNT_OFST        0x50

/*
 * Register : rb_pin_enabled
 * 
 * Interrupt or polling mode. Ready/Busy pin is enabled from device.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [0]    | RW     | 0x1   | ALT_NAND_CFG_RB_PIN_END_BANK0
 *  [1]    | RW     | 0x0   | ALT_NAND_CFG_RB_PIN_END_BANK1
 *  [2]    | RW     | 0x0   | ALT_NAND_CFG_RB_PIN_END_BANK2
 *  [3]    | RW     | 0x0   | ALT_NAND_CFG_RB_PIN_END_BANK3
 *  [31:4] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : bank0
 * 
 * Sets Denali Flash Controller in interrupt pin or polling mode [list][*]1 - R/B
 * pin enabled for bank 0. Interrupt pin mode. [*]0 - R/B pin disabled for bank 0.
 * Polling mode.[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_RB_PIN_END_BANK0 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_RB_PIN_END_BANK0 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK0_MSB        0
/* The width in bits of the ALT_NAND_CFG_RB_PIN_END_BANK0 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK0_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_RB_PIN_END_BANK0 register field value. */
#define ALT_NAND_CFG_RB_PIN_END_BANK0_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_RB_PIN_END_BANK0 register field value. */
#define ALT_NAND_CFG_RB_PIN_END_BANK0_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_RB_PIN_END_BANK0 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK0_RESET      0x1
/* Extracts the ALT_NAND_CFG_RB_PIN_END_BANK0 field value from a register. */
#define ALT_NAND_CFG_RB_PIN_END_BANK0_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_RB_PIN_END_BANK0 register field value suitable for setting the register. */
#define ALT_NAND_CFG_RB_PIN_END_BANK0_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : bank1
 * 
 * Sets Denali Flash Controller in interrupt pin or polling mode [list][*]1 - R/B
 * pin enabled for bank 1. Interrupt pin mode. [*]0 - R/B pin disabled for bank 1.
 * Polling mode.[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_RB_PIN_END_BANK1 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK1_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_RB_PIN_END_BANK1 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK1_MSB        1
/* The width in bits of the ALT_NAND_CFG_RB_PIN_END_BANK1 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK1_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_RB_PIN_END_BANK1 register field value. */
#define ALT_NAND_CFG_RB_PIN_END_BANK1_SET_MSK    0x00000002
/* The mask used to clear the ALT_NAND_CFG_RB_PIN_END_BANK1 register field value. */
#define ALT_NAND_CFG_RB_PIN_END_BANK1_CLR_MSK    0xfffffffd
/* The reset value of the ALT_NAND_CFG_RB_PIN_END_BANK1 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK1_RESET      0x0
/* Extracts the ALT_NAND_CFG_RB_PIN_END_BANK1 field value from a register. */
#define ALT_NAND_CFG_RB_PIN_END_BANK1_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_NAND_CFG_RB_PIN_END_BANK1 register field value suitable for setting the register. */
#define ALT_NAND_CFG_RB_PIN_END_BANK1_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : bank2
 * 
 * Sets Denali Flash Controller in interrupt pin or polling mode [list][*]1 - R/B
 * pin enabled for bank 2. Interrupt pin mode. [*]0 - R/B pin disabled for bank 2.
 * Polling mode.[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_RB_PIN_END_BANK2 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK2_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_RB_PIN_END_BANK2 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK2_MSB        2
/* The width in bits of the ALT_NAND_CFG_RB_PIN_END_BANK2 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK2_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_RB_PIN_END_BANK2 register field value. */
#define ALT_NAND_CFG_RB_PIN_END_BANK2_SET_MSK    0x00000004
/* The mask used to clear the ALT_NAND_CFG_RB_PIN_END_BANK2 register field value. */
#define ALT_NAND_CFG_RB_PIN_END_BANK2_CLR_MSK    0xfffffffb
/* The reset value of the ALT_NAND_CFG_RB_PIN_END_BANK2 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK2_RESET      0x0
/* Extracts the ALT_NAND_CFG_RB_PIN_END_BANK2 field value from a register. */
#define ALT_NAND_CFG_RB_PIN_END_BANK2_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_NAND_CFG_RB_PIN_END_BANK2 register field value suitable for setting the register. */
#define ALT_NAND_CFG_RB_PIN_END_BANK2_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : bank3
 * 
 * Sets Denali Flash Controller in interrupt pin or polling mode [list][*]1 - R/B
 * pin enabled for bank 3. Interrupt pin mode. [*]0 - R/B pin disabled for bank 3.
 * Polling mode.[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_RB_PIN_END_BANK3 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK3_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_RB_PIN_END_BANK3 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK3_MSB        3
/* The width in bits of the ALT_NAND_CFG_RB_PIN_END_BANK3 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK3_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_RB_PIN_END_BANK3 register field value. */
#define ALT_NAND_CFG_RB_PIN_END_BANK3_SET_MSK    0x00000008
/* The mask used to clear the ALT_NAND_CFG_RB_PIN_END_BANK3 register field value. */
#define ALT_NAND_CFG_RB_PIN_END_BANK3_CLR_MSK    0xfffffff7
/* The reset value of the ALT_NAND_CFG_RB_PIN_END_BANK3 register field. */
#define ALT_NAND_CFG_RB_PIN_END_BANK3_RESET      0x0
/* Extracts the ALT_NAND_CFG_RB_PIN_END_BANK3 field value from a register. */
#define ALT_NAND_CFG_RB_PIN_END_BANK3_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_NAND_CFG_RB_PIN_END_BANK3 register field value suitable for setting the register. */
#define ALT_NAND_CFG_RB_PIN_END_BANK3_SET(value) (((value) << 3) & 0x00000008)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_RB_PIN_END.
 */
struct ALT_NAND_CFG_RB_PIN_END_s
{
    uint32_t  bank0 :  1;  /* ALT_NAND_CFG_RB_PIN_END_BANK0 */
    uint32_t  bank1 :  1;  /* ALT_NAND_CFG_RB_PIN_END_BANK1 */
    uint32_t  bank2 :  1;  /* ALT_NAND_CFG_RB_PIN_END_BANK2 */
    uint32_t  bank3 :  1;  /* ALT_NAND_CFG_RB_PIN_END_BANK3 */
    uint32_t        : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_RB_PIN_END. */
typedef volatile struct ALT_NAND_CFG_RB_PIN_END_s  ALT_NAND_CFG_RB_PIN_END_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_RB_PIN_END register from the beginning of the component. */
#define ALT_NAND_CFG_RB_PIN_END_OFST        0x60

/*
 * Register : multiplane_operation
 * 
 * Multiplane transfer mode. Pipelined read, copyback, erase and program commands
 * are transfered in multiplane mode
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                    
 * :-------|:-------|:------|:--------------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_CFG_MULTIPLANE_OP_FLAG
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                    
 * 
 */
/*
 * Field : flag
 * 
 * [list][*]1 - Multiplane operation enabled [*]0 - Multiplane operation
 * disabled[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_MULTIPLANE_OP_FLAG register field. */
#define ALT_NAND_CFG_MULTIPLANE_OP_FLAG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_MULTIPLANE_OP_FLAG register field. */
#define ALT_NAND_CFG_MULTIPLANE_OP_FLAG_MSB        0
/* The width in bits of the ALT_NAND_CFG_MULTIPLANE_OP_FLAG register field. */
#define ALT_NAND_CFG_MULTIPLANE_OP_FLAG_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_MULTIPLANE_OP_FLAG register field value. */
#define ALT_NAND_CFG_MULTIPLANE_OP_FLAG_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_MULTIPLANE_OP_FLAG register field value. */
#define ALT_NAND_CFG_MULTIPLANE_OP_FLAG_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_MULTIPLANE_OP_FLAG register field. */
#define ALT_NAND_CFG_MULTIPLANE_OP_FLAG_RESET      0x0
/* Extracts the ALT_NAND_CFG_MULTIPLANE_OP_FLAG field value from a register. */
#define ALT_NAND_CFG_MULTIPLANE_OP_FLAG_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_MULTIPLANE_OP_FLAG register field value suitable for setting the register. */
#define ALT_NAND_CFG_MULTIPLANE_OP_FLAG_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_MULTIPLANE_OP.
 */
struct ALT_NAND_CFG_MULTIPLANE_OP_s
{
    uint32_t  flag :  1;  /* ALT_NAND_CFG_MULTIPLANE_OP_FLAG */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_MULTIPLANE_OP. */
typedef volatile struct ALT_NAND_CFG_MULTIPLANE_OP_s  ALT_NAND_CFG_MULTIPLANE_OP_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_MULTIPLANE_OP register from the beginning of the component. */
#define ALT_NAND_CFG_MULTIPLANE_OP_OFST        0x70

/*
 * Register : multiplane_read_enable
 * 
 * Device supports multiplane read command sequence
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                       
 * :-------|:-------|:------|:-----------------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                       
 * 
 */
/*
 * Field : flag
 * 
 * Certain devices support dedicated multiplane read command sequences to read data
 * in the same fashion as is written with multiplane program commands. This bit set
 * should be set for the above devices. When not set, pipeline reads in multiplane
 * mode will still happen in the order of multiplane writes, though normal read
 * command sequences will be issued to the device. [list][*]1 - Device supports
 * multiplane read sequence [*]0 - Device does not support multiplane read
 * sequence[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG register field. */
#define ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG register field. */
#define ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG_MSB        0
/* The width in bits of the ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG register field. */
#define ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG register field value. */
#define ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG register field value. */
#define ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG register field. */
#define ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG_RESET      0x0
/* Extracts the ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG field value from a register. */
#define ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG register field value suitable for setting the register. */
#define ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_MULTIPLANE_RD_EN.
 */
struct ALT_NAND_CFG_MULTIPLANE_RD_EN_s
{
    uint32_t  flag :  1;  /* ALT_NAND_CFG_MULTIPLANE_RD_EN_FLAG */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_MULTIPLANE_RD_EN. */
typedef volatile struct ALT_NAND_CFG_MULTIPLANE_RD_EN_s  ALT_NAND_CFG_MULTIPLANE_RD_EN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_MULTIPLANE_RD_EN register from the beginning of the component. */
#define ALT_NAND_CFG_MULTIPLANE_RD_EN_OFST        0x80

/*
 * Register : copyback_disable
 * 
 * Device does not support copyback command sequence
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                   
 * :-------|:-------|:------|:-------------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_CFG_COPYBACK_DIS_FLAG
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                   
 * 
 */
/*
 * Field : flag
 * 
 * [list][*]1 - Copyback disabled [*]0 - Copyback enabled[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_COPYBACK_DIS_FLAG register field. */
#define ALT_NAND_CFG_COPYBACK_DIS_FLAG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_COPYBACK_DIS_FLAG register field. */
#define ALT_NAND_CFG_COPYBACK_DIS_FLAG_MSB        0
/* The width in bits of the ALT_NAND_CFG_COPYBACK_DIS_FLAG register field. */
#define ALT_NAND_CFG_COPYBACK_DIS_FLAG_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_COPYBACK_DIS_FLAG register field value. */
#define ALT_NAND_CFG_COPYBACK_DIS_FLAG_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_COPYBACK_DIS_FLAG register field value. */
#define ALT_NAND_CFG_COPYBACK_DIS_FLAG_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_COPYBACK_DIS_FLAG register field. */
#define ALT_NAND_CFG_COPYBACK_DIS_FLAG_RESET      0x0
/* Extracts the ALT_NAND_CFG_COPYBACK_DIS_FLAG field value from a register. */
#define ALT_NAND_CFG_COPYBACK_DIS_FLAG_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_COPYBACK_DIS_FLAG register field value suitable for setting the register. */
#define ALT_NAND_CFG_COPYBACK_DIS_FLAG_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_COPYBACK_DIS.
 */
struct ALT_NAND_CFG_COPYBACK_DIS_s
{
    uint32_t  flag :  1;  /* ALT_NAND_CFG_COPYBACK_DIS_FLAG */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_COPYBACK_DIS. */
typedef volatile struct ALT_NAND_CFG_COPYBACK_DIS_s  ALT_NAND_CFG_COPYBACK_DIS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_COPYBACK_DIS register from the beginning of the component. */
#define ALT_NAND_CFG_COPYBACK_DIS_OFST        0x90

/*
 * Register : cache_write_enable
 * 
 * Device supports cache write command sequence
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_CFG_CACHE_WR_EN_FLAG
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : flag
 * 
 * [list][*]1 - Cache write supported [*]0 - Cache write not supported[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_CACHE_WR_EN_FLAG register field. */
#define ALT_NAND_CFG_CACHE_WR_EN_FLAG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_CACHE_WR_EN_FLAG register field. */
#define ALT_NAND_CFG_CACHE_WR_EN_FLAG_MSB        0
/* The width in bits of the ALT_NAND_CFG_CACHE_WR_EN_FLAG register field. */
#define ALT_NAND_CFG_CACHE_WR_EN_FLAG_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_CACHE_WR_EN_FLAG register field value. */
#define ALT_NAND_CFG_CACHE_WR_EN_FLAG_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_CACHE_WR_EN_FLAG register field value. */
#define ALT_NAND_CFG_CACHE_WR_EN_FLAG_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_CACHE_WR_EN_FLAG register field. */
#define ALT_NAND_CFG_CACHE_WR_EN_FLAG_RESET      0x0
/* Extracts the ALT_NAND_CFG_CACHE_WR_EN_FLAG field value from a register. */
#define ALT_NAND_CFG_CACHE_WR_EN_FLAG_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_CACHE_WR_EN_FLAG register field value suitable for setting the register. */
#define ALT_NAND_CFG_CACHE_WR_EN_FLAG_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_CACHE_WR_EN.
 */
struct ALT_NAND_CFG_CACHE_WR_EN_s
{
    uint32_t  flag :  1;  /* ALT_NAND_CFG_CACHE_WR_EN_FLAG */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_CACHE_WR_EN. */
typedef volatile struct ALT_NAND_CFG_CACHE_WR_EN_s  ALT_NAND_CFG_CACHE_WR_EN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_CACHE_WR_EN register from the beginning of the component. */
#define ALT_NAND_CFG_CACHE_WR_EN_OFST        0xa0

/*
 * Register : cache_read_enable
 * 
 * Device supports cache read command sequence
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_CFG_CACHE_RD_EN_FLAG
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : flag
 * 
 * [list][*]1 - Cache read supported [*]0 - Cache read not supported[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_CACHE_RD_EN_FLAG register field. */
#define ALT_NAND_CFG_CACHE_RD_EN_FLAG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_CACHE_RD_EN_FLAG register field. */
#define ALT_NAND_CFG_CACHE_RD_EN_FLAG_MSB        0
/* The width in bits of the ALT_NAND_CFG_CACHE_RD_EN_FLAG register field. */
#define ALT_NAND_CFG_CACHE_RD_EN_FLAG_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_CACHE_RD_EN_FLAG register field value. */
#define ALT_NAND_CFG_CACHE_RD_EN_FLAG_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_CACHE_RD_EN_FLAG register field value. */
#define ALT_NAND_CFG_CACHE_RD_EN_FLAG_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_CACHE_RD_EN_FLAG register field. */
#define ALT_NAND_CFG_CACHE_RD_EN_FLAG_RESET      0x0
/* Extracts the ALT_NAND_CFG_CACHE_RD_EN_FLAG field value from a register. */
#define ALT_NAND_CFG_CACHE_RD_EN_FLAG_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_CACHE_RD_EN_FLAG register field value suitable for setting the register. */
#define ALT_NAND_CFG_CACHE_RD_EN_FLAG_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_CACHE_RD_EN.
 */
struct ALT_NAND_CFG_CACHE_RD_EN_s
{
    uint32_t  flag :  1;  /* ALT_NAND_CFG_CACHE_RD_EN_FLAG */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_CACHE_RD_EN. */
typedef volatile struct ALT_NAND_CFG_CACHE_RD_EN_s  ALT_NAND_CFG_CACHE_RD_EN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_CACHE_RD_EN register from the beginning of the component. */
#define ALT_NAND_CFG_CACHE_RD_EN_OFST        0xb0

/*
 * Register : prefetch_mode
 * 
 * Enables read data prefetching to faster performance
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                 
 * :--------|:-------|:------|:---------------------------------------------
 *  [0]     | RW     | 0x1   | ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN       
 *  [3:1]   | ???    | 0x0   | *UNDEFINED*                                 
 *  [15:4]  | RW     | 0x0   | ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                                 
 * 
 */
/*
 * Field : prefetch_en
 * 
 * Enable prefetch of Data
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN register field. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN register field. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN_MSB        0
/* The width in bits of the ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN register field. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN register field value. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN register field value. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN register field. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN_RESET      0x1
/* Extracts the ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN field value from a register. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN register field value suitable for setting the register. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : prefetch_burst_length
 * 
 * If prefetch_en is set and prefetch_burst_length is set to ZERO, the controller
 * will start prefetching data only after the receiving the first Map01 read
 * command for the page. If prefetch_en is set and prefetch_burst_length is set to
 * a non-ZERO, valid value, the controller will start prefetching data
 * corresponding to this value even before the first Map01 for the current page has
 * been received. The value written here should be in bytes.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN register field. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN register field. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN_MSB        15
/* The width in bits of the ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN register field. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN_WIDTH      12
/* The mask used to set the ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN register field value. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN_SET_MSK    0x0000fff0
/* The mask used to clear the ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN register field value. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN_CLR_MSK    0xffff000f
/* The reset value of the ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN register field. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN_RESET      0x0
/* Extracts the ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN field value from a register. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN_GET(value) (((value) & 0x0000fff0) >> 4)
/* Produces a ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN register field value suitable for setting the register. */
#define ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN_SET(value) (((value) << 4) & 0x0000fff0)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_PREFETCH_MOD.
 */
struct ALT_NAND_CFG_PREFETCH_MOD_s
{
    uint32_t  prefetch_en           :  1;  /* ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_EN */
    uint32_t                        :  3;  /* *UNDEFINED* */
    uint32_t  prefetch_burst_length : 12;  /* ALT_NAND_CFG_PREFETCH_MOD_PREFETCH_BURST_LEN */
    uint32_t                        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_PREFETCH_MOD. */
typedef volatile struct ALT_NAND_CFG_PREFETCH_MOD_s  ALT_NAND_CFG_PREFETCH_MOD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_PREFETCH_MOD register from the beginning of the component. */
#define ALT_NAND_CFG_PREFETCH_MOD_OFST        0xc0

/*
 * Register : chip_enable_dont_care
 * 
 * Device can work in the chip enable dont care mode
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                        
 * :-------|:-------|:------|:------------------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : flag
 * 
 * Controller can interleave commands between banks when this feature is enabled.
 * [list][*]1 - Device in dont care mode [*]0 - Device cares for chip enable[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG register field. */
#define ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG register field. */
#define ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG_MSB        0
/* The width in bits of the ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG register field. */
#define ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG register field value. */
#define ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG register field value. */
#define ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG register field. */
#define ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG_RESET      0x0
/* Extracts the ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG field value from a register. */
#define ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG register field value suitable for setting the register. */
#define ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_CHIP_EN_DONT_CARE.
 */
struct ALT_NAND_CFG_CHIP_EN_DONT_CARE_s
{
    uint32_t  flag :  1;  /* ALT_NAND_CFG_CHIP_EN_DONT_CARE_FLAG */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_CHIP_EN_DONT_CARE. */
typedef volatile struct ALT_NAND_CFG_CHIP_EN_DONT_CARE_s  ALT_NAND_CFG_CHIP_EN_DONT_CARE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_CHIP_EN_DONT_CARE register from the beginning of the component. */
#define ALT_NAND_CFG_CHIP_EN_DONT_CARE_OFST        0xd0

/*
 * Register : ecc_enable
 * 
 * Enable controller ECC check bit generation and correction
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description             
 * :-------|:-------|:------|:-------------------------
 *  [0]    | RW     | 0x1   | ALT_NAND_CFG_ECC_EN_FLAG
 *  [31:1] | ???    | 0x0   | *UNDEFINED*             
 * 
 */
/*
 * Field : flag
 * 
 * Enables or disables controller ECC capabilities. When enabled, controller
 * calculates ECC check-bits and writes them onto device on program operation. On
 * page reads, check-bits are recomputed and errors reported, if any, after
 * comparing with stored check-bits. When disabled, controller does not compute
 * check-bits. [list][*]1 - ECC Enabled [*]0 - ECC disabled[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_ECC_EN_FLAG register field. */
#define ALT_NAND_CFG_ECC_EN_FLAG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_ECC_EN_FLAG register field. */
#define ALT_NAND_CFG_ECC_EN_FLAG_MSB        0
/* The width in bits of the ALT_NAND_CFG_ECC_EN_FLAG register field. */
#define ALT_NAND_CFG_ECC_EN_FLAG_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_ECC_EN_FLAG register field value. */
#define ALT_NAND_CFG_ECC_EN_FLAG_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_ECC_EN_FLAG register field value. */
#define ALT_NAND_CFG_ECC_EN_FLAG_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_ECC_EN_FLAG register field. */
#define ALT_NAND_CFG_ECC_EN_FLAG_RESET      0x1
/* Extracts the ALT_NAND_CFG_ECC_EN_FLAG field value from a register. */
#define ALT_NAND_CFG_ECC_EN_FLAG_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_ECC_EN_FLAG register field value suitable for setting the register. */
#define ALT_NAND_CFG_ECC_EN_FLAG_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_ECC_EN.
 */
struct ALT_NAND_CFG_ECC_EN_s
{
    uint32_t  flag :  1;  /* ALT_NAND_CFG_ECC_EN_FLAG */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_ECC_EN. */
typedef volatile struct ALT_NAND_CFG_ECC_EN_s  ALT_NAND_CFG_ECC_EN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_ECC_EN register from the beginning of the component. */
#define ALT_NAND_CFG_ECC_EN_OFST        0xe0

/*
 * Register : global_int_enable
 * 
 * Global Interrupt enable and Error/Timeout disable.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                           
 * :-------|:-------|:------|:---------------------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_CFG_GLOB_INT_EN_FLAG         
 *  [3:1]  | ???    | 0x0   | *UNDEFINED*                           
 *  [4]    | RW     | 0x0   | ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS      
 *  [7:5]  | ???    | 0x0   | *UNDEFINED*                           
 *  [8]    | RW     | 0x0   | ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS
 *  [31:9] | ???    | 0x0   | *UNDEFINED*                           
 * 
 */
/*
 * Field : flag
 * 
 * Host will receive an interrupt only when this bit is set.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_GLOB_INT_EN_FLAG register field. */
#define ALT_NAND_CFG_GLOB_INT_EN_FLAG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_GLOB_INT_EN_FLAG register field. */
#define ALT_NAND_CFG_GLOB_INT_EN_FLAG_MSB        0
/* The width in bits of the ALT_NAND_CFG_GLOB_INT_EN_FLAG register field. */
#define ALT_NAND_CFG_GLOB_INT_EN_FLAG_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_GLOB_INT_EN_FLAG register field value. */
#define ALT_NAND_CFG_GLOB_INT_EN_FLAG_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_GLOB_INT_EN_FLAG register field value. */
#define ALT_NAND_CFG_GLOB_INT_EN_FLAG_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_GLOB_INT_EN_FLAG register field. */
#define ALT_NAND_CFG_GLOB_INT_EN_FLAG_RESET      0x0
/* Extracts the ALT_NAND_CFG_GLOB_INT_EN_FLAG field value from a register. */
#define ALT_NAND_CFG_GLOB_INT_EN_FLAG_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_GLOB_INT_EN_FLAG register field value suitable for setting the register. */
#define ALT_NAND_CFG_GLOB_INT_EN_FLAG_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : timeout_disable
 * 
 * Watchdog timer logic will be de-activated when this bit is set.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS register field. */
#define ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS register field. */
#define ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS_MSB        4
/* The width in bits of the ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS register field. */
#define ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS register field value. */
#define ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS_SET_MSK    0x00000010
/* The mask used to clear the ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS register field value. */
#define ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS_CLR_MSK    0xffffffef
/* The reset value of the ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS register field. */
#define ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS_RESET      0x0
/* Extracts the ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS field value from a register. */
#define ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS register field value suitable for setting the register. */
#define ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : error_rpt_disable
 * 
 * Command and ECC uncorrectable failures will not be reported when this bit is set
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS register field. */
#define ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS register field. */
#define ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS_MSB        8
/* The width in bits of the ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS register field. */
#define ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS register field value. */
#define ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS_SET_MSK    0x00000100
/* The mask used to clear the ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS register field value. */
#define ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS_CLR_MSK    0xfffffeff
/* The reset value of the ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS register field. */
#define ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS_RESET      0x0
/* Extracts the ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS field value from a register. */
#define ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS register field value suitable for setting the register. */
#define ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS_SET(value) (((value) << 8) & 0x00000100)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_GLOB_INT_EN.
 */
struct ALT_NAND_CFG_GLOB_INT_EN_s
{
    uint32_t  flag              :  1;  /* ALT_NAND_CFG_GLOB_INT_EN_FLAG */
    uint32_t                    :  3;  /* *UNDEFINED* */
    uint32_t  timeout_disable   :  1;  /* ALT_NAND_CFG_GLOB_INT_EN_TMO_DIS */
    uint32_t                    :  3;  /* *UNDEFINED* */
    uint32_t  error_rpt_disable :  1;  /* ALT_NAND_CFG_GLOB_INT_EN_ERROR_RPT_DIS */
    uint32_t                    : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_GLOB_INT_EN. */
typedef volatile struct ALT_NAND_CFG_GLOB_INT_EN_s  ALT_NAND_CFG_GLOB_INT_EN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_GLOB_INT_EN register from the beginning of the component. */
#define ALT_NAND_CFG_GLOB_INT_EN_OFST        0xf0

/*
 * Register : twhr2_and_we_2_re
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                           
 * :--------|:-------|:------|:---------------------------------------
 *  [5:0]   | RW     | 0x32  | ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE
 *  [7:6]   | ???    | 0x0   | *UNDEFINED*                           
 *  [13:8]  | RW     | 0x14  | ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2  
 *  [31:14] | ???    | 0x0   | *UNDEFINED*                           
 * 
 */
/*
 * Field : we_2_re
 * 
 * Signifies the number of bus interface nand_mp_clk clocks that should be
 * introduced between write enable going high to read enable going low. The number
 * of clocks is the function of device parameter Twhr and controller clock
 * frequency.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE register field. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE register field. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE_MSB        5
/* The width in bits of the ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE register field. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE_WIDTH      6
/* The mask used to set the ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE register field value. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE_SET_MSK    0x0000003f
/* The mask used to clear the ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE register field value. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE_CLR_MSK    0xffffffc0
/* The reset value of the ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE register field. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE_RESET      0x32
/* Extracts the ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE field value from a register. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE_GET(value) (((value) & 0x0000003f) >> 0)
/* Produces a ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE register field value suitable for setting the register. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE_SET(value) (((value) << 0) & 0x0000003f)

/*
 * Field : twhr2
 * 
 * Signifies the number of controller clocks that should be introduced between the
 * last command of a random data output command to the start of the data transfer.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2 register field. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2 register field. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2_MSB        13
/* The width in bits of the ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2 register field. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2_WIDTH      6
/* The mask used to set the ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2 register field value. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2_SET_MSK    0x00003f00
/* The mask used to clear the ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2 register field value. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2_CLR_MSK    0xffffc0ff
/* The reset value of the ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2 register field. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2_RESET      0x14
/* Extracts the ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2 field value from a register. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2_GET(value) (((value) & 0x00003f00) >> 8)
/* Produces a ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2 register field value suitable for setting the register. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2_SET(value) (((value) << 8) & 0x00003f00)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_TWHR2_AND_WE_2_RE.
 */
struct ALT_NAND_CFG_TWHR2_AND_WE_2_RE_s
{
    uint32_t  we_2_re :  6;  /* ALT_NAND_CFG_TWHR2_AND_WE_2_RE_WE_2_RE */
    uint32_t          :  2;  /* *UNDEFINED* */
    uint32_t  twhr2   :  6;  /* ALT_NAND_CFG_TWHR2_AND_WE_2_RE_TWHR2 */
    uint32_t          : 18;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_TWHR2_AND_WE_2_RE. */
typedef volatile struct ALT_NAND_CFG_TWHR2_AND_WE_2_RE_s  ALT_NAND_CFG_TWHR2_AND_WE_2_RE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_TWHR2_AND_WE_2_RE register from the beginning of the component. */
#define ALT_NAND_CFG_TWHR2_AND_WE_2_RE_OFST        0x100

/*
 * Register : tcwaw_and_addr_2_data
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                   
 * :--------|:-------|:------|:-----------------------------------------------
 *  [5:0]   | RW     | 0x32  | ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA
 *  [7:6]   | ???    | 0x0   | *UNDEFINED*                                   
 *  [13:8]  | RW     | 0x14  | ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW      
 *  [31:14] | ???    | 0x0   | *UNDEFINED*                                   
 * 
 */
/*
 * Field : addr_2_data
 * 
 * Signifies the number of bus interface nand_mp_clk clocks that should be
 * introduced between address latch enable going low to write enable going low. The
 * number of clocks is the function of device parameter Tadl and controller clock
 * frequency.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA register field. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA register field. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA_MSB        5
/* The width in bits of the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA register field. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA_WIDTH      6
/* The mask used to set the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA register field value. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA_SET_MSK    0x0000003f
/* The mask used to clear the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA register field value. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA_CLR_MSK    0xffffffc0
/* The reset value of the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA register field. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA_RESET      0x32
/* Extracts the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA field value from a register. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA_GET(value) (((value) & 0x0000003f) >> 0)
/* Produces a ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA register field value suitable for setting the register. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA_SET(value) (((value) << 0) & 0x0000003f)

/*
 * Field : tcwaw
 * 
 * Signifies the number of controller clocks that should be introduced between the
 * command cycle of a random data input command to the address cycle of the random
 * data input command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW register field. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW register field. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW_MSB        13
/* The width in bits of the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW register field. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW_WIDTH      6
/* The mask used to set the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW register field value. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW_SET_MSK    0x00003f00
/* The mask used to clear the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW register field value. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW_CLR_MSK    0xffffc0ff
/* The reset value of the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW register field. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW_RESET      0x14
/* Extracts the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW field value from a register. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW_GET(value) (((value) & 0x00003f00) >> 8)
/* Produces a ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW register field value suitable for setting the register. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW_SET(value) (((value) << 8) & 0x00003f00)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA.
 */
struct ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_s
{
    uint32_t  addr_2_data :  6;  /* ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_ADDR_2_DATA */
    uint32_t              :  2;  /* *UNDEFINED* */
    uint32_t  tcwaw       :  6;  /* ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_TCWAW */
    uint32_t              : 18;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA. */
typedef volatile struct ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_s  ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA register from the beginning of the component. */
#define ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_OFST        0x110

/*
 * Register : re_2_we
 * 
 * Timing parameter between re high to we low (Trhw)
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description               
 * :-------|:-------|:------|:---------------------------
 *  [5:0]  | RW     | 0x32  | ALT_NAND_CFG_RE_2_WE_VALUE
 *  [31:6] | ???    | 0x0   | *UNDEFINED*               
 * 
 */
/*
 * Field : value
 * 
 * Signifies the number of bus interface nand_mp_clk clocks that should be
 * introduced between read enable going high to write enable going low. The number
 * of clocks is the function of device parameter Trhw and controller clock
 * frequency.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_RE_2_WE_VALUE register field. */
#define ALT_NAND_CFG_RE_2_WE_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_RE_2_WE_VALUE register field. */
#define ALT_NAND_CFG_RE_2_WE_VALUE_MSB        5
/* The width in bits of the ALT_NAND_CFG_RE_2_WE_VALUE register field. */
#define ALT_NAND_CFG_RE_2_WE_VALUE_WIDTH      6
/* The mask used to set the ALT_NAND_CFG_RE_2_WE_VALUE register field value. */
#define ALT_NAND_CFG_RE_2_WE_VALUE_SET_MSK    0x0000003f
/* The mask used to clear the ALT_NAND_CFG_RE_2_WE_VALUE register field value. */
#define ALT_NAND_CFG_RE_2_WE_VALUE_CLR_MSK    0xffffffc0
/* The reset value of the ALT_NAND_CFG_RE_2_WE_VALUE register field. */
#define ALT_NAND_CFG_RE_2_WE_VALUE_RESET      0x32
/* Extracts the ALT_NAND_CFG_RE_2_WE_VALUE field value from a register. */
#define ALT_NAND_CFG_RE_2_WE_VALUE_GET(value) (((value) & 0x0000003f) >> 0)
/* Produces a ALT_NAND_CFG_RE_2_WE_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_RE_2_WE_VALUE_SET(value) (((value) << 0) & 0x0000003f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_RE_2_WE.
 */
struct ALT_NAND_CFG_RE_2_WE_s
{
    uint32_t  value :  6;  /* ALT_NAND_CFG_RE_2_WE_VALUE */
    uint32_t        : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_RE_2_WE. */
typedef volatile struct ALT_NAND_CFG_RE_2_WE_s  ALT_NAND_CFG_RE_2_WE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_RE_2_WE register from the beginning of the component. */
#define ALT_NAND_CFG_RE_2_WE_OFST        0x120

/*
 * Register : acc_clks
 * 
 * Timing parameter from read enable going low to capture read data
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                
 * :-------|:-------|:------|:----------------------------
 *  [3:0]  | RW     | 0x0   | ALT_NAND_CFG_ACC_CLKS_VALUE
 *  [31:4] | ???    | 0x0   | *UNDEFINED*                
 * 
 */
/*
 * Field : value
 * 
 * Signifies the number of bus interface nand_mp_clk clock cycles, controller
 * should wait from read enable going low to sending out a strobe of nand_mp_clk
 * for capturing of incoming data.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_ACC_CLKS_VALUE register field. */
#define ALT_NAND_CFG_ACC_CLKS_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_ACC_CLKS_VALUE register field. */
#define ALT_NAND_CFG_ACC_CLKS_VALUE_MSB        3
/* The width in bits of the ALT_NAND_CFG_ACC_CLKS_VALUE register field. */
#define ALT_NAND_CFG_ACC_CLKS_VALUE_WIDTH      4
/* The mask used to set the ALT_NAND_CFG_ACC_CLKS_VALUE register field value. */
#define ALT_NAND_CFG_ACC_CLKS_VALUE_SET_MSK    0x0000000f
/* The mask used to clear the ALT_NAND_CFG_ACC_CLKS_VALUE register field value. */
#define ALT_NAND_CFG_ACC_CLKS_VALUE_CLR_MSK    0xfffffff0
/* The reset value of the ALT_NAND_CFG_ACC_CLKS_VALUE register field. */
#define ALT_NAND_CFG_ACC_CLKS_VALUE_RESET      0x0
/* Extracts the ALT_NAND_CFG_ACC_CLKS_VALUE field value from a register. */
#define ALT_NAND_CFG_ACC_CLKS_VALUE_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_NAND_CFG_ACC_CLKS_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_ACC_CLKS_VALUE_SET(value) (((value) << 0) & 0x0000000f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_ACC_CLKS.
 */
struct ALT_NAND_CFG_ACC_CLKS_s
{
    uint32_t  value :  4;  /* ALT_NAND_CFG_ACC_CLKS_VALUE */
    uint32_t        : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_ACC_CLKS. */
typedef volatile struct ALT_NAND_CFG_ACC_CLKS_s  ALT_NAND_CFG_ACC_CLKS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_ACC_CLKS register from the beginning of the component. */
#define ALT_NAND_CFG_ACC_CLKS_OFST        0x130

/*
 * Register : number_of_planes
 * 
 * Number of planes in the device
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                        
 * :-------|:-------|:------|:------------------------------------
 *  [2:0]  | RW     | 0x0   | ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE
 *  [31:3] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : value
 * 
 * Controller will read Electronic Signature of devices and populate this field as
 * the number of planes information is present in the signature. For 512B device,
 * this information needs to be programmed by software. Software could also choose
 * to override the populated value. The values in the fields should be as
 * follows[list] [*]3'h0 - Monoplane device [*]3'h1 - Two plane device [*]3'h3 - 4
 * plane device [*]3'h7 - 8 plane device [*]All other values - Reserved[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE register field. */
#define ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE register field. */
#define ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE_MSB        2
/* The width in bits of the ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE register field. */
#define ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE_WIDTH      3
/* The mask used to set the ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE register field value. */
#define ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE_SET_MSK    0x00000007
/* The mask used to clear the ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE register field value. */
#define ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE_CLR_MSK    0xfffffff8
/* The reset value of the ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE register field. */
#define ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE_RESET      0x0
/* Extracts the ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE field value from a register. */
#define ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE_GET(value) (((value) & 0x00000007) >> 0)
/* Produces a ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE_SET(value) (((value) << 0) & 0x00000007)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_NUMBER_OF_PLANES.
 */
struct ALT_NAND_CFG_NUMBER_OF_PLANES_s
{
    uint32_t  value :  3;  /* ALT_NAND_CFG_NUMBER_OF_PLANES_VALUE */
    uint32_t        : 29;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_NUMBER_OF_PLANES. */
typedef volatile struct ALT_NAND_CFG_NUMBER_OF_PLANES_s  ALT_NAND_CFG_NUMBER_OF_PLANES_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_NUMBER_OF_PLANES register from the beginning of the component. */
#define ALT_NAND_CFG_NUMBER_OF_PLANES_OFST        0x140

/*
 * Register : pages_per_block
 * 
 * Number of pages in a block
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                       
 * :--------|:-------|:------|:-----------------------------------
 *  [15:0]  | RW     | 0x0   | ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                       
 * 
 */
/*
 * Field : value
 * 
 * Controller will read Electronic Signature of devices and populate this field.
 * The PAGE512 field of the System Manager NANDGRP_BOOTSTRAP register will
 * determine the value of this field to be of 32. Software could also choose to
 * override the populated value.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE register field. */
#define ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE register field. */
#define ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE_MSB        15
/* The width in bits of the ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE register field. */
#define ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE register field value. */
#define ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE register field value. */
#define ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE register field. */
#define ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE_RESET      0x0
/* Extracts the ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE field value from a register. */
#define ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_PAGES_PER_BLOCK.
 */
struct ALT_NAND_CFG_PAGES_PER_BLOCK_s
{
    uint32_t  value : 16;  /* ALT_NAND_CFG_PAGES_PER_BLOCK_VALUE */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_PAGES_PER_BLOCK. */
typedef volatile struct ALT_NAND_CFG_PAGES_PER_BLOCK_s  ALT_NAND_CFG_PAGES_PER_BLOCK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_PAGES_PER_BLOCK register from the beginning of the component. */
#define ALT_NAND_CFG_PAGES_PER_BLOCK_OFST        0x150

/*
 * Register : device_width
 * 
 * I/O width of attached devices
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                    
 * :-------|:-------|:------|:--------------------------------
 *  [1:0]  | RW     | 0x3   | ALT_NAND_CFG_DEVICE_WIDTH_VALUE
 *  [31:2] | ???    | 0x0   | *UNDEFINED*                    
 * 
 */
/*
 * Field : value
 * 
 * Controller will read Electronic Signature of devices and populate this field.
 * Software could also choose to override the populated value although only one
 * value is supported. The values in this field should be as follows[list][*]2'h00
 * - 8bit device[*]All other values - Reserved[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_DEVICE_WIDTH_VALUE register field. */
#define ALT_NAND_CFG_DEVICE_WIDTH_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_DEVICE_WIDTH_VALUE register field. */
#define ALT_NAND_CFG_DEVICE_WIDTH_VALUE_MSB        1
/* The width in bits of the ALT_NAND_CFG_DEVICE_WIDTH_VALUE register field. */
#define ALT_NAND_CFG_DEVICE_WIDTH_VALUE_WIDTH      2
/* The mask used to set the ALT_NAND_CFG_DEVICE_WIDTH_VALUE register field value. */
#define ALT_NAND_CFG_DEVICE_WIDTH_VALUE_SET_MSK    0x00000003
/* The mask used to clear the ALT_NAND_CFG_DEVICE_WIDTH_VALUE register field value. */
#define ALT_NAND_CFG_DEVICE_WIDTH_VALUE_CLR_MSK    0xfffffffc
/* The reset value of the ALT_NAND_CFG_DEVICE_WIDTH_VALUE register field. */
#define ALT_NAND_CFG_DEVICE_WIDTH_VALUE_RESET      0x3
/* Extracts the ALT_NAND_CFG_DEVICE_WIDTH_VALUE field value from a register. */
#define ALT_NAND_CFG_DEVICE_WIDTH_VALUE_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_NAND_CFG_DEVICE_WIDTH_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_DEVICE_WIDTH_VALUE_SET(value) (((value) << 0) & 0x00000003)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_DEVICE_WIDTH.
 */
struct ALT_NAND_CFG_DEVICE_WIDTH_s
{
    uint32_t  value :  2;  /* ALT_NAND_CFG_DEVICE_WIDTH_VALUE */
    uint32_t        : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_DEVICE_WIDTH. */
typedef volatile struct ALT_NAND_CFG_DEVICE_WIDTH_s  ALT_NAND_CFG_DEVICE_WIDTH_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_DEVICE_WIDTH register from the beginning of the component. */
#define ALT_NAND_CFG_DEVICE_WIDTH_OFST        0x160

/*
 * Register : device_main_area_size
 * 
 * Page main area size of device in bytes
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                             
 * :--------|:-------|:------|:-----------------------------------------
 *  [15:0]  | RW     | 0x0   | ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                             
 * 
 */
/*
 * Field : value
 * 
 * Controller will read Electronic Signature of devices and populate this field.
 * The PAGE512 field of the System Manager NANDGRP_BOOTSTRAP register will
 * determine the value of this field to be 512. Software could also choose to
 * override the populated value.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE register field. */
#define ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE register field. */
#define ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE_MSB        15
/* The width in bits of the ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE register field. */
#define ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE register field value. */
#define ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE register field value. */
#define ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE register field. */
#define ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE_RESET      0x0
/* Extracts the ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE field value from a register. */
#define ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE.
 */
struct ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_s
{
    uint32_t  value : 16;  /* ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_VALUE */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE. */
typedef volatile struct ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_s  ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE register from the beginning of the component. */
#define ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_OFST        0x170

/*
 * Register : device_spare_area_size
 * 
 * Page spare area size of device in bytes
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                              
 * :--------|:-------|:------|:------------------------------------------
 *  [15:0]  | RW     | 0x0   | ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                              
 * 
 */
/*
 * Field : value
 * 
 * Controller will read Electronic Signature of devices and populate this field.
 * The PAGE512 field of the System Manager NANDGRP_BOOTSTRAP register will
 * determine the value of this field to be 16. Software could also choose to
 * override the populated value.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE register field. */
#define ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE register field. */
#define ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE_MSB        15
/* The width in bits of the ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE register field. */
#define ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE register field value. */
#define ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE register field value. */
#define ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE register field. */
#define ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE_RESET      0x0
/* Extracts the ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE field value from a register. */
#define ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE.
 */
struct ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_s
{
    uint32_t  value : 16;  /* ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_VALUE */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE. */
typedef volatile struct ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_s  ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE register from the beginning of the component. */
#define ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_OFST        0x180

/*
 * Register : two_row_addr_cycles
 * 
 * Attached device has only 2 ROW address cycles
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                          
 * :-------|:-------|:------|:--------------------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                          
 * 
 */
/*
 * Field : flag
 * 
 * This flag must be set for devices which allow for 2 ROW address cycles instead
 * of the usual 3. Alternatively, the TWOROWADDR field of the System Manager
 * NANDGRP_BOOTSTRAP register when asserted will set this flag.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG register field. */
#define ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG register field. */
#define ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG_MSB        0
/* The width in bits of the ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG register field. */
#define ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG register field value. */
#define ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG register field value. */
#define ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG register field. */
#define ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG_RESET      0x0
/* Extracts the ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG field value from a register. */
#define ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG register field value suitable for setting the register. */
#define ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES.
 */
struct ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_s
{
    uint32_t  flag :  1;  /* ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_FLAG */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES. */
typedef volatile struct ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_s  ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES register from the beginning of the component. */
#define ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_OFST        0x190

/*
 * Register : multiplane_addr_restrict
 * 
 * Address restriction for multiplane commands
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                               
 * :-------|:-------|:------|:-------------------------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                               
 * 
 */
/*
 * Field : flag
 * 
 * This flag must be set for devices which require that during multiplane
 * operations all but the address for the last plane should have their address
 * cycles tied low. The last plane address cycles has proper values. This ensures
 * multiplane address restrictions in the device.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG register field. */
#define ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG register field. */
#define ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG_MSB        0
/* The width in bits of the ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG register field. */
#define ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG register field value. */
#define ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG register field value. */
#define ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG register field. */
#define ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG_RESET      0x0
/* Extracts the ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG field value from a register. */
#define ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG register field value suitable for setting the register. */
#define ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT.
 */
struct ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_s
{
    uint32_t  flag :  1;  /* ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_FLAG */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT. */
typedef volatile struct ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_s  ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT register from the beginning of the component. */
#define ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_OFST        0x1a0

/*
 * Register : ecc_correction
 * 
 * Correction capability required
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                      
 * :-------|:-------|:------|:----------------------------------
 *  [7:0]  | RW     | 0x8   | ALT_NAND_CFG_ECC_CORRECTION_VALUE
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                      
 * 
 */
/*
 * Field : value
 * 
 * The required correction capability can be a number less than the configured
 * error correction capability. A smaller correction capability will lead to lesser
 * number of ECC check-bits being written per ECC sector.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_ECC_CORRECTION_VALUE register field. */
#define ALT_NAND_CFG_ECC_CORRECTION_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_ECC_CORRECTION_VALUE register field. */
#define ALT_NAND_CFG_ECC_CORRECTION_VALUE_MSB        7
/* The width in bits of the ALT_NAND_CFG_ECC_CORRECTION_VALUE register field. */
#define ALT_NAND_CFG_ECC_CORRECTION_VALUE_WIDTH      8
/* The mask used to set the ALT_NAND_CFG_ECC_CORRECTION_VALUE register field value. */
#define ALT_NAND_CFG_ECC_CORRECTION_VALUE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_NAND_CFG_ECC_CORRECTION_VALUE register field value. */
#define ALT_NAND_CFG_ECC_CORRECTION_VALUE_CLR_MSK    0xffffff00
/* The reset value of the ALT_NAND_CFG_ECC_CORRECTION_VALUE register field. */
#define ALT_NAND_CFG_ECC_CORRECTION_VALUE_RESET      0x8
/* Extracts the ALT_NAND_CFG_ECC_CORRECTION_VALUE field value from a register. */
#define ALT_NAND_CFG_ECC_CORRECTION_VALUE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_NAND_CFG_ECC_CORRECTION_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_ECC_CORRECTION_VALUE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_ECC_CORRECTION.
 */
struct ALT_NAND_CFG_ECC_CORRECTION_s
{
    uint32_t  value :  8;  /* ALT_NAND_CFG_ECC_CORRECTION_VALUE */
    uint32_t        : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_ECC_CORRECTION. */
typedef volatile struct ALT_NAND_CFG_ECC_CORRECTION_s  ALT_NAND_CFG_ECC_CORRECTION_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_ECC_CORRECTION register from the beginning of the component. */
#define ALT_NAND_CFG_ECC_CORRECTION_OFST        0x1b0

/*
 * Register : read_mode
 * 
 * The type of read sequence that the controller will follow for pipe read
 * commands.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description              
 * :-------|:-------|:------|:--------------------------
 *  [3:0]  | RW     | 0x0   | ALT_NAND_CFG_RD_MOD_VALUE
 *  [31:4] | ???    | 0x0   | *UNDEFINED*              
 * 
 */
/*
 * Field : value
 * 
 * The values in the field should be as follows[list] [*]4'h0 - This value informs
 * the controller that the pipe read sequence to follow is of a normal read. For
 * 512 byte page devices, Normal read sequence is, C00, Address, Data, ..... For
 * devices with page size greater that 512 bytes, the sequence is, C00, Address,
 * C30, Data..... [*]4'h1 - This value informs the controller that the pipe read
 * sequence to follow is of a Cache Read with the following sequence, C00, Address,
 * C30, C31, Data, C31, Data, ....., C3F, Data. [*]4'h2 - This value informs the
 * controller that the pipe read sequence to follow is of a Cache Read with the
 * following sequence, C00, Address, C31, Data, Data, ....., C34. [*]4'h3 - This
 * value informs the controller that the pipe read sequence to follow is of a 'N'
 * Plane Read with the following sequence, C00, Address, C00, Address, C30, Data,
 * C06, Address, CE0, Data..... [*]4'h4 - This value informs the controller that
 * the pipe read sequence to follow is of a 'N' Plane Read with the following
 * sequence, C60, Address, C60, Address, C30, C00, Address, C05, Address, CE0,
 * Data, C00, Address, C05, Address, CE0, Data..... [*]4'h5 - This value informs
 * the controller that the pipe read sequence to follow is of a 'N' Plane Cache
 * Read with the following sequence, C60, Address, C60, Address, C30, C31, C00,
 * Address, C05, Address, CE0, Data, C00, Address, C05, Address, CE0, Data, .....,
 * C3F, C00, Address, C05, Address, CE0, Data, C00, Address, C05, Address, CE0,
 * Data [*]4'h6 - This value informs the controller that the pipe read sequence to
 * follow is of a 'N' Plane Read with the following sequence, C00, Address, C32,
 * .., C00, Address, C30, C06, Address, CE0, Data, C06, Address, CE0, Data,....
 * [*]4'h7 - This value informs the controller that the pipe read sequence to
 * follow is of a 'N' Plane Cache Read with the following sequence, C00, Address,
 * C32,..., C00, Address, C30, C31,C06, Address, CE0, Data, C31, C06, Address, CE0,
 * Data, C3F, C06, Address, CE0, Data.... [*]4'h8 - This value informs the
 * controller that the pipe read sequence to follow is of a 'N' Plane Cache Read
 * with the following sequence, C60, Address, C60, Address, C33, C31, C00, Address,
 * C05, Address, CE0, Data, C00, Address, C05, Address, CE0, Data, ....., C3F, C00,
 * Address, C05, Address, CE0, Data, C00, Address, C05, Address, CE0, Data [*]4'h9
 * - 4'h15 - Reserved. [/list] ..... indicates that the previous sequence is
 * repeated till the last page.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_RD_MOD_VALUE register field. */
#define ALT_NAND_CFG_RD_MOD_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_RD_MOD_VALUE register field. */
#define ALT_NAND_CFG_RD_MOD_VALUE_MSB        3
/* The width in bits of the ALT_NAND_CFG_RD_MOD_VALUE register field. */
#define ALT_NAND_CFG_RD_MOD_VALUE_WIDTH      4
/* The mask used to set the ALT_NAND_CFG_RD_MOD_VALUE register field value. */
#define ALT_NAND_CFG_RD_MOD_VALUE_SET_MSK    0x0000000f
/* The mask used to clear the ALT_NAND_CFG_RD_MOD_VALUE register field value. */
#define ALT_NAND_CFG_RD_MOD_VALUE_CLR_MSK    0xfffffff0
/* The reset value of the ALT_NAND_CFG_RD_MOD_VALUE register field. */
#define ALT_NAND_CFG_RD_MOD_VALUE_RESET      0x0
/* Extracts the ALT_NAND_CFG_RD_MOD_VALUE field value from a register. */
#define ALT_NAND_CFG_RD_MOD_VALUE_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_NAND_CFG_RD_MOD_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_RD_MOD_VALUE_SET(value) (((value) << 0) & 0x0000000f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_RD_MOD.
 */
struct ALT_NAND_CFG_RD_MOD_s
{
    uint32_t  value :  4;  /* ALT_NAND_CFG_RD_MOD_VALUE */
    uint32_t        : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_RD_MOD. */
typedef volatile struct ALT_NAND_CFG_RD_MOD_s  ALT_NAND_CFG_RD_MOD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_RD_MOD register from the beginning of the component. */
#define ALT_NAND_CFG_RD_MOD_OFST        0x1c0

/*
 * Register : write_mode
 * 
 * The type of write sequence that the controller will follow for pipe write
 * commands.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description              
 * :-------|:-------|:------|:--------------------------
 *  [3:0]  | RW     | 0x0   | ALT_NAND_CFG_WR_MOD_VALUE
 *  [31:4] | ???    | 0x0   | *UNDEFINED*              
 * 
 */
/*
 * Field : value
 * 
 * The values in the field should be as follows[list] [*]4'h0 - This value informs
 * the controller that the pipe write sequence to follow is of a normal write with
 * the following sequence, C80, Address, Data, C10..... [*]4'h1 - This value
 * informs the controller that the pipe write sequence to follow is of a Cache
 * Program with the following sequence, C80, Address, Data, C15, ....., C80,
 * Address, Data, C10. [*]4'h2 - This value informs the controller that the pipe
 * write sequence to follow is of a Two/Four Plane Program with the following
 * sequence, C80, Address, Data, C11, C81, Address, Data, C10..... [*]4'h3 - This
 * value informs the controller that the pipe write sequence to follow is of a 'N'
 * Plane Program with the following sequence, C80, Address, Data, C11, C80,
 * Address, Data, C10..... [*]4'h4 - This value informs the controller that the
 * pipe write sequence to follow is of a 'N' Plane Cache Program with the following
 * sequence, C80, Address, Data, C11, C80, Address, Data, C15.....C80, Address,
 * Data, C11, C80, Address, Data, C10. [*]4'h5 - This value informs the controller
 * that the pipe write sequence to follow is of a 'N' Plane Cache Program with the
 * following sequence, C80, Address, Data, C11, C81, Address, Data, C15.....C80,
 * Address, Data, C11, C81, Address, Data, C10. [*]4'h6 - 4'h15 - Reserved. [/list]
 * ..... indicates that the previous sequence is repeated till the last page.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_WR_MOD_VALUE register field. */
#define ALT_NAND_CFG_WR_MOD_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_WR_MOD_VALUE register field. */
#define ALT_NAND_CFG_WR_MOD_VALUE_MSB        3
/* The width in bits of the ALT_NAND_CFG_WR_MOD_VALUE register field. */
#define ALT_NAND_CFG_WR_MOD_VALUE_WIDTH      4
/* The mask used to set the ALT_NAND_CFG_WR_MOD_VALUE register field value. */
#define ALT_NAND_CFG_WR_MOD_VALUE_SET_MSK    0x0000000f
/* The mask used to clear the ALT_NAND_CFG_WR_MOD_VALUE register field value. */
#define ALT_NAND_CFG_WR_MOD_VALUE_CLR_MSK    0xfffffff0
/* The reset value of the ALT_NAND_CFG_WR_MOD_VALUE register field. */
#define ALT_NAND_CFG_WR_MOD_VALUE_RESET      0x0
/* Extracts the ALT_NAND_CFG_WR_MOD_VALUE field value from a register. */
#define ALT_NAND_CFG_WR_MOD_VALUE_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_NAND_CFG_WR_MOD_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_WR_MOD_VALUE_SET(value) (((value) << 0) & 0x0000000f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_WR_MOD.
 */
struct ALT_NAND_CFG_WR_MOD_s
{
    uint32_t  value :  4;  /* ALT_NAND_CFG_WR_MOD_VALUE */
    uint32_t        : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_WR_MOD. */
typedef volatile struct ALT_NAND_CFG_WR_MOD_s  ALT_NAND_CFG_WR_MOD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_WR_MOD register from the beginning of the component. */
#define ALT_NAND_CFG_WR_MOD_OFST        0x1d0

/*
 * Register : copyback_mode
 * 
 * The type of copyback sequence that the controller will follow.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                    
 * :-------|:-------|:------|:--------------------------------
 *  [3:0]  | RW     | 0x0   | ALT_NAND_CFG_COPYBACK_MOD_VALUE
 *  [31:4] | ???    | 0x0   | *UNDEFINED*                    
 * 
 */
/*
 * Field : value
 * 
 * The values in the field should be as follows[list] [*]4'h0 - This value informs
 * the controller that the copyback sequence to follow is, C00, Address, C35, C85,
 * Address, C10 [*]4'h1 - This value informs the controller that the copyback
 * sequence to follow is, C00, Address, C30, C8C, Address, C10 [*]4'h2 - This value
 * informs the controller that the copyback sequence to follow is, C00, Address,
 * C8A, Address, C10 [*]4'h3 - This value informs the controller that the copyback
 * sequence to follow is of a four plane copyback sequence, C00, Address, C03,
 * Address, C03, Address, C03, Address, C8A, Address, C11, C8A, Address, C11, C8A,
 * Address, C11, C8A, Address, C10. [*]4'h4 - This value informs the controller
 * that the copyback sequence to follow is of a two plane copyback sequence, C00,
 * Address, C35, C00, Address, C35, C85, Address, C11, C81, Address, C10. [*]4'h5 -
 * This value informs the controller that the copyback sequence to follow is of a
 * two plane copyback sequence, C60, Address, C60, Address, C35, C85, Address, C11,
 * C81, Address, C10. [*]4'h6 - This value informs the controller that the copyback
 * sequence to follow is of a two plane copyback sequence, C00, Address, C00,
 * Address, C35, C85, Address, C11, C80, Address, C10. [*]4'h7 - This value informs
 * the controller that the copyback sequence to follow is of a two plane copyback
 * sequence, C60, Address, C60, Address, C30, C8C, Address, C11, C8C, Address, C10.
 * [*]4'h8 - 4'h15 - Reserved.[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_COPYBACK_MOD_VALUE register field. */
#define ALT_NAND_CFG_COPYBACK_MOD_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_COPYBACK_MOD_VALUE register field. */
#define ALT_NAND_CFG_COPYBACK_MOD_VALUE_MSB        3
/* The width in bits of the ALT_NAND_CFG_COPYBACK_MOD_VALUE register field. */
#define ALT_NAND_CFG_COPYBACK_MOD_VALUE_WIDTH      4
/* The mask used to set the ALT_NAND_CFG_COPYBACK_MOD_VALUE register field value. */
#define ALT_NAND_CFG_COPYBACK_MOD_VALUE_SET_MSK    0x0000000f
/* The mask used to clear the ALT_NAND_CFG_COPYBACK_MOD_VALUE register field value. */
#define ALT_NAND_CFG_COPYBACK_MOD_VALUE_CLR_MSK    0xfffffff0
/* The reset value of the ALT_NAND_CFG_COPYBACK_MOD_VALUE register field. */
#define ALT_NAND_CFG_COPYBACK_MOD_VALUE_RESET      0x0
/* Extracts the ALT_NAND_CFG_COPYBACK_MOD_VALUE field value from a register. */
#define ALT_NAND_CFG_COPYBACK_MOD_VALUE_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_NAND_CFG_COPYBACK_MOD_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_COPYBACK_MOD_VALUE_SET(value) (((value) << 0) & 0x0000000f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_COPYBACK_MOD.
 */
struct ALT_NAND_CFG_COPYBACK_MOD_s
{
    uint32_t  value :  4;  /* ALT_NAND_CFG_COPYBACK_MOD_VALUE */
    uint32_t        : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_COPYBACK_MOD. */
typedef volatile struct ALT_NAND_CFG_COPYBACK_MOD_s  ALT_NAND_CFG_COPYBACK_MOD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_COPYBACK_MOD register from the beginning of the component. */
#define ALT_NAND_CFG_COPYBACK_MOD_OFST        0x1e0

/*
 * Register : rdwr_en_lo_cnt
 * 
 * Read/Write Enable low pulse width
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                      
 * :-------|:-------|:------|:----------------------------------
 *  [4:0]  | RW     | 0x12  | ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE
 *  [31:5] | ???    | 0x0   | *UNDEFINED*                      
 * 
 */
/*
 * Field : value
 * 
 * Number of nand_mp_clk cycles that read or write enable will kept low to meet the
 * min Trp/Twp parameter of the device. The value in this register plus
 * rdwr_en_hi_cnt register value should meet the min cycle time of the device
 * connected. The default value is calculated assuming the max nand_mp_clk time
 * period of 4ns to work with ONFI Mode 0 mode of 100ns device cycle time. This
 * assumes a 1x/4x clocking scheme.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE register field. */
#define ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE register field. */
#define ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE_MSB        4
/* The width in bits of the ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE register field. */
#define ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE_WIDTH      5
/* The mask used to set the ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE register field value. */
#define ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE_SET_MSK    0x0000001f
/* The mask used to clear the ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE register field value. */
#define ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE_CLR_MSK    0xffffffe0
/* The reset value of the ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE register field. */
#define ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE_RESET      0x12
/* Extracts the ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE field value from a register. */
#define ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE_GET(value) (((value) & 0x0000001f) >> 0)
/* Produces a ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE_SET(value) (((value) << 0) & 0x0000001f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_RDWR_EN_LO_CNT.
 */
struct ALT_NAND_CFG_RDWR_EN_LO_CNT_s
{
    uint32_t  value :  5;  /* ALT_NAND_CFG_RDWR_EN_LO_CNT_VALUE */
    uint32_t        : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_RDWR_EN_LO_CNT. */
typedef volatile struct ALT_NAND_CFG_RDWR_EN_LO_CNT_s  ALT_NAND_CFG_RDWR_EN_LO_CNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_RDWR_EN_LO_CNT register from the beginning of the component. */
#define ALT_NAND_CFG_RDWR_EN_LO_CNT_OFST        0x1f0

/*
 * Register : rdwr_en_hi_cnt
 * 
 * Read/Write Enable high pulse width
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                      
 * :-------|:-------|:------|:----------------------------------
 *  [4:0]  | RW     | 0xc   | ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE
 *  [31:5] | ???    | 0x0   | *UNDEFINED*                      
 * 
 */
/*
 * Field : value
 * 
 * Number of nand_mp_clk cycles that read or write enable will kept high to meet
 * the min Treh/Tweh parameter of the device. The value in this register plus
 * rdwr_en_lo_cnt register value should meet the min cycle time of the device
 * connected. The default value is calculated assuming the max nand_mp_clk time
 * period of 4ns to work with ONFI Mode 0 mode of 100ns device cycle time. This
 * assumes a 1x/4x clocking scheme.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE register field. */
#define ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE register field. */
#define ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE_MSB        4
/* The width in bits of the ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE register field. */
#define ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE_WIDTH      5
/* The mask used to set the ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE register field value. */
#define ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE_SET_MSK    0x0000001f
/* The mask used to clear the ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE register field value. */
#define ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE_CLR_MSK    0xffffffe0
/* The reset value of the ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE register field. */
#define ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE_RESET      0xc
/* Extracts the ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE field value from a register. */
#define ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE_GET(value) (((value) & 0x0000001f) >> 0)
/* Produces a ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE_SET(value) (((value) << 0) & 0x0000001f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_RDWR_EN_HI_CNT.
 */
struct ALT_NAND_CFG_RDWR_EN_HI_CNT_s
{
    uint32_t  value :  5;  /* ALT_NAND_CFG_RDWR_EN_HI_CNT_VALUE */
    uint32_t        : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_RDWR_EN_HI_CNT. */
typedef volatile struct ALT_NAND_CFG_RDWR_EN_HI_CNT_s  ALT_NAND_CFG_RDWR_EN_HI_CNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_RDWR_EN_HI_CNT register from the beginning of the component. */
#define ALT_NAND_CFG_RDWR_EN_HI_CNT_OFST        0x200

/*
 * Register : max_rd_delay
 * 
 * Max round trip read data delay for data capture
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                    
 * :-------|:-------|:------|:--------------------------------
 *  [3:0]  | RW     | 0x0   | ALT_NAND_CFG_MAX_RD_DELAY_VALUE
 *  [31:4] | ???    | 0x0   | *UNDEFINED*                    
 * 
 */
/*
 * Field : value
 * 
 * Number of nand_mp_clk cycles after generation of feedback nand_mp_clk pulse when
 * it is safe to synchronize received data to nand_mp_clk domain. Data should have
 * been registered with nand_mp_clk and stable by the time max_rd_delay cycles has
 * elapsed. A default value of zero will mean a value of nand_mp_clk multiple minus
 * one.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_MAX_RD_DELAY_VALUE register field. */
#define ALT_NAND_CFG_MAX_RD_DELAY_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_MAX_RD_DELAY_VALUE register field. */
#define ALT_NAND_CFG_MAX_RD_DELAY_VALUE_MSB        3
/* The width in bits of the ALT_NAND_CFG_MAX_RD_DELAY_VALUE register field. */
#define ALT_NAND_CFG_MAX_RD_DELAY_VALUE_WIDTH      4
/* The mask used to set the ALT_NAND_CFG_MAX_RD_DELAY_VALUE register field value. */
#define ALT_NAND_CFG_MAX_RD_DELAY_VALUE_SET_MSK    0x0000000f
/* The mask used to clear the ALT_NAND_CFG_MAX_RD_DELAY_VALUE register field value. */
#define ALT_NAND_CFG_MAX_RD_DELAY_VALUE_CLR_MSK    0xfffffff0
/* The reset value of the ALT_NAND_CFG_MAX_RD_DELAY_VALUE register field. */
#define ALT_NAND_CFG_MAX_RD_DELAY_VALUE_RESET      0x0
/* Extracts the ALT_NAND_CFG_MAX_RD_DELAY_VALUE field value from a register. */
#define ALT_NAND_CFG_MAX_RD_DELAY_VALUE_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_NAND_CFG_MAX_RD_DELAY_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_MAX_RD_DELAY_VALUE_SET(value) (((value) << 0) & 0x0000000f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_MAX_RD_DELAY.
 */
struct ALT_NAND_CFG_MAX_RD_DELAY_s
{
    uint32_t  value :  4;  /* ALT_NAND_CFG_MAX_RD_DELAY_VALUE */
    uint32_t        : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_MAX_RD_DELAY. */
typedef volatile struct ALT_NAND_CFG_MAX_RD_DELAY_s  ALT_NAND_CFG_MAX_RD_DELAY_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_MAX_RD_DELAY register from the beginning of the component. */
#define ALT_NAND_CFG_MAX_RD_DELAY_OFST        0x210

/*
 * Register : cs_setup_cnt
 * 
 * Chip select setup time
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                    
 * :-------|:-------|:------|:--------------------------------
 *  [4:0]  | RW     | 0x3   | ALT_NAND_CFG_CS_SETUP_CNT_VALUE
 *  [31:5] | ???    | 0x0   | *UNDEFINED*                    
 * 
 */
/*
 * Field : value
 * 
 * Number of nand_mp_clk cycles required for meeting chip select setup time. This
 * register refers to device timing parameter Tcs. The value in this registers
 * reflects the extra setup cycles for chip select before read/write enable signal
 * is set low. The default value is calculated for ONFI Timing mode 0 Tcs = 70ns
 * and maximum nand_mp_clk period of 4ns for 1x/4x clock multiple for 16ns cycle
 * time device. Please refer to Figure 3.3 for the relationship between the
 * cs_setup_cnt and rdwr_en_lo_cnt values.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_CS_SETUP_CNT_VALUE register field. */
#define ALT_NAND_CFG_CS_SETUP_CNT_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_CS_SETUP_CNT_VALUE register field. */
#define ALT_NAND_CFG_CS_SETUP_CNT_VALUE_MSB        4
/* The width in bits of the ALT_NAND_CFG_CS_SETUP_CNT_VALUE register field. */
#define ALT_NAND_CFG_CS_SETUP_CNT_VALUE_WIDTH      5
/* The mask used to set the ALT_NAND_CFG_CS_SETUP_CNT_VALUE register field value. */
#define ALT_NAND_CFG_CS_SETUP_CNT_VALUE_SET_MSK    0x0000001f
/* The mask used to clear the ALT_NAND_CFG_CS_SETUP_CNT_VALUE register field value. */
#define ALT_NAND_CFG_CS_SETUP_CNT_VALUE_CLR_MSK    0xffffffe0
/* The reset value of the ALT_NAND_CFG_CS_SETUP_CNT_VALUE register field. */
#define ALT_NAND_CFG_CS_SETUP_CNT_VALUE_RESET      0x3
/* Extracts the ALT_NAND_CFG_CS_SETUP_CNT_VALUE field value from a register. */
#define ALT_NAND_CFG_CS_SETUP_CNT_VALUE_GET(value) (((value) & 0x0000001f) >> 0)
/* Produces a ALT_NAND_CFG_CS_SETUP_CNT_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_CS_SETUP_CNT_VALUE_SET(value) (((value) << 0) & 0x0000001f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_CS_SETUP_CNT.
 */
struct ALT_NAND_CFG_CS_SETUP_CNT_s
{
    uint32_t  value :  5;  /* ALT_NAND_CFG_CS_SETUP_CNT_VALUE */
    uint32_t        : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_CS_SETUP_CNT. */
typedef volatile struct ALT_NAND_CFG_CS_SETUP_CNT_s  ALT_NAND_CFG_CS_SETUP_CNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_CS_SETUP_CNT register from the beginning of the component. */
#define ALT_NAND_CFG_CS_SETUP_CNT_OFST        0x220

/*
 * Register : spare_area_skip_bytes
 * 
 * Spare area skip bytes
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                             
 * :-------|:-------|:------|:-----------------------------------------
 *  [5:0]  | RW     | 0x0   | ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE
 *  [31:6] | ???    | 0x0   | *UNDEFINED*                             
 * 
 */
/*
 * Field : value
 * 
 * Number of bytes to skip from start of spare area before last ECC sector data
 * starts. The bytes will be written with the value programmed in the
 * spare_area_marker register. This register could be potentially used to preserve
 * the bad block marker in the spare area by marking it good. The default value is
 * zero which means no bytes will be skipped and last ECC sector will start from
 * the beginning of spare area.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE register field. */
#define ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE register field. */
#define ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE_MSB        5
/* The width in bits of the ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE register field. */
#define ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE_WIDTH      6
/* The mask used to set the ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE register field value. */
#define ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE_SET_MSK    0x0000003f
/* The mask used to clear the ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE register field value. */
#define ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE_CLR_MSK    0xffffffc0
/* The reset value of the ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE register field. */
#define ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE_RESET      0x0
/* Extracts the ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE field value from a register. */
#define ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE_GET(value) (((value) & 0x0000003f) >> 0)
/* Produces a ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE_SET(value) (((value) << 0) & 0x0000003f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES.
 */
struct ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_s
{
    uint32_t  value :  6;  /* ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_VALUE */
    uint32_t        : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES. */
typedef volatile struct ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_s  ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES register from the beginning of the component. */
#define ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_OFST        0x230

/*
 * Register : spare_area_marker
 * 
 * Spare area marker value
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset  | Description                         
 * :--------|:-------|:-------|:-------------------------------------
 *  [15:0]  | RW     | 0xffff | ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE
 *  [31:16] | ???    | 0x0    | *UNDEFINED*                         
 * 
 */
/*
 * Field : value
 * 
 * The value that will be written in the spare area skip bytes. This value will be
 * used by controller while in the MAIN mode of data transfer. Only the least-
 * significant 8 bits of the field value are used.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE register field. */
#define ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE register field. */
#define ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE_MSB        15
/* The width in bits of the ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE register field. */
#define ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE register field value. */
#define ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE register field value. */
#define ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE register field. */
#define ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE_RESET      0xffff
/* Extracts the ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE field value from a register. */
#define ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_SPARE_AREA_MARKER.
 */
struct ALT_NAND_CFG_SPARE_AREA_MARKER_s
{
    uint32_t  value : 16;  /* ALT_NAND_CFG_SPARE_AREA_MARKER_VALUE */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_SPARE_AREA_MARKER. */
typedef volatile struct ALT_NAND_CFG_SPARE_AREA_MARKER_s  ALT_NAND_CFG_SPARE_AREA_MARKER_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_SPARE_AREA_MARKER register from the beginning of the component. */
#define ALT_NAND_CFG_SPARE_AREA_MARKER_OFST        0x240

/*
 * Register : devices_connected
 * 
 * Number of Devices connected on one bank
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                         
 * :-------|:-------|:------|:-------------------------------------
 *  [2:0]  | RW     | 0x0   | ALT_NAND_CFG_DEVICES_CONNECTED_VALUE
 *  [31:3] | ???    | 0x0   | *UNDEFINED*                         
 * 
 */
/*
 * Field : value
 * 
 * Indicates the number of devices connected to a bank. At reset, the value loaded
 * is the maximum possible devices that could be connected in this configuration.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_DEVICES_CONNECTED_VALUE register field. */
#define ALT_NAND_CFG_DEVICES_CONNECTED_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_DEVICES_CONNECTED_VALUE register field. */
#define ALT_NAND_CFG_DEVICES_CONNECTED_VALUE_MSB        2
/* The width in bits of the ALT_NAND_CFG_DEVICES_CONNECTED_VALUE register field. */
#define ALT_NAND_CFG_DEVICES_CONNECTED_VALUE_WIDTH      3
/* The mask used to set the ALT_NAND_CFG_DEVICES_CONNECTED_VALUE register field value. */
#define ALT_NAND_CFG_DEVICES_CONNECTED_VALUE_SET_MSK    0x00000007
/* The mask used to clear the ALT_NAND_CFG_DEVICES_CONNECTED_VALUE register field value. */
#define ALT_NAND_CFG_DEVICES_CONNECTED_VALUE_CLR_MSK    0xfffffff8
/* The reset value of the ALT_NAND_CFG_DEVICES_CONNECTED_VALUE register field. */
#define ALT_NAND_CFG_DEVICES_CONNECTED_VALUE_RESET      0x0
/* Extracts the ALT_NAND_CFG_DEVICES_CONNECTED_VALUE field value from a register. */
#define ALT_NAND_CFG_DEVICES_CONNECTED_VALUE_GET(value) (((value) & 0x00000007) >> 0)
/* Produces a ALT_NAND_CFG_DEVICES_CONNECTED_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_DEVICES_CONNECTED_VALUE_SET(value) (((value) << 0) & 0x00000007)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_DEVICES_CONNECTED.
 */
struct ALT_NAND_CFG_DEVICES_CONNECTED_s
{
    uint32_t  value :  3;  /* ALT_NAND_CFG_DEVICES_CONNECTED_VALUE */
    uint32_t        : 29;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_DEVICES_CONNECTED. */
typedef volatile struct ALT_NAND_CFG_DEVICES_CONNECTED_s  ALT_NAND_CFG_DEVICES_CONNECTED_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_DEVICES_CONNECTED register from the beginning of the component. */
#define ALT_NAND_CFG_DEVICES_CONNECTED_OFST        0x250

/*
 * Register : die_mask
 * 
 * Indicates the die differentiator in case of NAND devices with stacked dies.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description               
 * :-------|:-------|:------|:---------------------------
 *  [7:0]  | RW     | 0x0   | ALT_NAND_CFG_DIE_MSK_VALUE
 *  [31:8] | ???    | 0x0   | *UNDEFINED*               
 * 
 */
/*
 * Field : value
 * 
 * The die_mask register information will be used for devices having address
 * restrictions. For example, in certain Samsung devices, when the first address in
 * a two-plane command is being sent, it is expected that the address is all zeros.
 * But if the NAND device internally has multiple dies stacked, the die information
 * (MSB of final row address) has to be sent. The value programmed in this register
 * will be used to mask the address while sending out the last row address.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_DIE_MSK_VALUE register field. */
#define ALT_NAND_CFG_DIE_MSK_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_DIE_MSK_VALUE register field. */
#define ALT_NAND_CFG_DIE_MSK_VALUE_MSB        7
/* The width in bits of the ALT_NAND_CFG_DIE_MSK_VALUE register field. */
#define ALT_NAND_CFG_DIE_MSK_VALUE_WIDTH      8
/* The mask used to set the ALT_NAND_CFG_DIE_MSK_VALUE register field value. */
#define ALT_NAND_CFG_DIE_MSK_VALUE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_NAND_CFG_DIE_MSK_VALUE register field value. */
#define ALT_NAND_CFG_DIE_MSK_VALUE_CLR_MSK    0xffffff00
/* The reset value of the ALT_NAND_CFG_DIE_MSK_VALUE register field. */
#define ALT_NAND_CFG_DIE_MSK_VALUE_RESET      0x0
/* Extracts the ALT_NAND_CFG_DIE_MSK_VALUE field value from a register. */
#define ALT_NAND_CFG_DIE_MSK_VALUE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_NAND_CFG_DIE_MSK_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_DIE_MSK_VALUE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_DIE_MSK.
 */
struct ALT_NAND_CFG_DIE_MSK_s
{
    uint32_t  value :  8;  /* ALT_NAND_CFG_DIE_MSK_VALUE */
    uint32_t        : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_DIE_MSK. */
typedef volatile struct ALT_NAND_CFG_DIE_MSK_s  ALT_NAND_CFG_DIE_MSK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_DIE_MSK register from the beginning of the component. */
#define ALT_NAND_CFG_DIE_MSK_OFST        0x260

/*
 * Register : first_block_of_next_plane
 * 
 * The starting block address of the next plane in a multi plane device.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                 
 * :--------|:-------|:------|:---------------------------------------------
 *  [15:0]  | RW     | 0x1   | ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                                 
 * 
 */
/*
 * Field : value
 * 
 * This values informs the controller of the plane structure of the device. In case
 * the device is a multi plane device and the value here is 1, the controller
 * understands that the next plane starts from Block number 1 and in conjunction
 * with the number of planes parameter can decide upon the distribution of blocks
 * in a plane in the device.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE register field. */
#define ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE register field. */
#define ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE_MSB        15
/* The width in bits of the ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE register field. */
#define ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE register field value. */
#define ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE register field value. */
#define ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE register field. */
#define ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE_RESET      0x1
/* Extracts the ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE field value from a register. */
#define ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE.
 */
struct ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_s
{
    uint32_t  value : 16;  /* ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_VALUE */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE. */
typedef volatile struct ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_s  ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE register from the beginning of the component. */
#define ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_OFST        0x270

/*
 * Register : write_protect
 * 
 * This register is used to control the assertion/de-assertion of the WP# pin to
 * the device.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                 
 * :-------|:-------|:------|:-----------------------------
 *  [0]    | RW     | 0x1   | ALT_NAND_CFG_WR_PROTECT_FLAG
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                 
 * 
 */
/*
 * Field : flag
 * 
 * When the controller is in reset, the WP# pin is always asserted to the device.
 * Once the reset is removed, the WP# is de-asserted. The software will then have
 * to come and program this bit to assert/de-assert the same. [list][*]1 - Write
 * protect de-assert [*]0 - Write protect assert[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_WR_PROTECT_FLAG register field. */
#define ALT_NAND_CFG_WR_PROTECT_FLAG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_WR_PROTECT_FLAG register field. */
#define ALT_NAND_CFG_WR_PROTECT_FLAG_MSB        0
/* The width in bits of the ALT_NAND_CFG_WR_PROTECT_FLAG register field. */
#define ALT_NAND_CFG_WR_PROTECT_FLAG_WIDTH      1
/* The mask used to set the ALT_NAND_CFG_WR_PROTECT_FLAG register field value. */
#define ALT_NAND_CFG_WR_PROTECT_FLAG_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_CFG_WR_PROTECT_FLAG register field value. */
#define ALT_NAND_CFG_WR_PROTECT_FLAG_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_CFG_WR_PROTECT_FLAG register field. */
#define ALT_NAND_CFG_WR_PROTECT_FLAG_RESET      0x1
/* Extracts the ALT_NAND_CFG_WR_PROTECT_FLAG field value from a register. */
#define ALT_NAND_CFG_WR_PROTECT_FLAG_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_CFG_WR_PROTECT_FLAG register field value suitable for setting the register. */
#define ALT_NAND_CFG_WR_PROTECT_FLAG_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_WR_PROTECT.
 */
struct ALT_NAND_CFG_WR_PROTECT_s
{
    uint32_t  flag :  1;  /* ALT_NAND_CFG_WR_PROTECT_FLAG */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_WR_PROTECT. */
typedef volatile struct ALT_NAND_CFG_WR_PROTECT_s  ALT_NAND_CFG_WR_PROTECT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_WR_PROTECT register from the beginning of the component. */
#define ALT_NAND_CFG_WR_PROTECT_OFST        0x280

/*
 * Register : re_2_re
 * 
 * Timing parameter between re high to re low (Trhz) for the next bank
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description               
 * :-------|:-------|:------|:---------------------------
 *  [5:0]  | RW     | 0x32  | ALT_NAND_CFG_RE_2_RE_VALUE
 *  [31:6] | ???    | 0x0   | *UNDEFINED*               
 * 
 */
/*
 * Field : value
 * 
 * Signifies the number of bus interface nand_mp_clk clocks that should be
 * introduced between read enable going high to a bank to the read enable going low
 * to the next bank. The number of clocks is the function of device parameter Trhz
 * and controller clock frequency.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_RE_2_RE_VALUE register field. */
#define ALT_NAND_CFG_RE_2_RE_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_RE_2_RE_VALUE register field. */
#define ALT_NAND_CFG_RE_2_RE_VALUE_MSB        5
/* The width in bits of the ALT_NAND_CFG_RE_2_RE_VALUE register field. */
#define ALT_NAND_CFG_RE_2_RE_VALUE_WIDTH      6
/* The mask used to set the ALT_NAND_CFG_RE_2_RE_VALUE register field value. */
#define ALT_NAND_CFG_RE_2_RE_VALUE_SET_MSK    0x0000003f
/* The mask used to clear the ALT_NAND_CFG_RE_2_RE_VALUE register field value. */
#define ALT_NAND_CFG_RE_2_RE_VALUE_CLR_MSK    0xffffffc0
/* The reset value of the ALT_NAND_CFG_RE_2_RE_VALUE register field. */
#define ALT_NAND_CFG_RE_2_RE_VALUE_RESET      0x32
/* Extracts the ALT_NAND_CFG_RE_2_RE_VALUE field value from a register. */
#define ALT_NAND_CFG_RE_2_RE_VALUE_GET(value) (((value) & 0x0000003f) >> 0)
/* Produces a ALT_NAND_CFG_RE_2_RE_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_RE_2_RE_VALUE_SET(value) (((value) << 0) & 0x0000003f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_RE_2_RE.
 */
struct ALT_NAND_CFG_RE_2_RE_s
{
    uint32_t  value :  6;  /* ALT_NAND_CFG_RE_2_RE_VALUE */
    uint32_t        : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_RE_2_RE. */
typedef volatile struct ALT_NAND_CFG_RE_2_RE_s  ALT_NAND_CFG_RE_2_RE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_RE_2_RE register from the beginning of the component. */
#define ALT_NAND_CFG_RE_2_RE_OFST        0x290

/*
 * Register : por_reset_count
 * 
 * The number of cycles the controller waits after reset to issue the first RESET
 * command to the device.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                     
 * :--------|:-------|:------|:---------------------------------
 *  [15:0]  | RW     | 0x13b | ALT_NAND_CFG_POR_RST_COUNT_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                     
 * 
 */
/*
 * Field : value
 * 
 * The controller waits for this number of cycles before issuing the first RESET
 * command to the device. The number in this register is multiplied internally by
 * 16 in the controller to form the final reset wait count.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_POR_RST_COUNT_VALUE register field. */
#define ALT_NAND_CFG_POR_RST_COUNT_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_POR_RST_COUNT_VALUE register field. */
#define ALT_NAND_CFG_POR_RST_COUNT_VALUE_MSB        15
/* The width in bits of the ALT_NAND_CFG_POR_RST_COUNT_VALUE register field. */
#define ALT_NAND_CFG_POR_RST_COUNT_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_CFG_POR_RST_COUNT_VALUE register field value. */
#define ALT_NAND_CFG_POR_RST_COUNT_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_CFG_POR_RST_COUNT_VALUE register field value. */
#define ALT_NAND_CFG_POR_RST_COUNT_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_CFG_POR_RST_COUNT_VALUE register field. */
#define ALT_NAND_CFG_POR_RST_COUNT_VALUE_RESET      0x13b
/* Extracts the ALT_NAND_CFG_POR_RST_COUNT_VALUE field value from a register. */
#define ALT_NAND_CFG_POR_RST_COUNT_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_CFG_POR_RST_COUNT_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_POR_RST_COUNT_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_POR_RST_COUNT.
 */
struct ALT_NAND_CFG_POR_RST_COUNT_s
{
    uint32_t  value : 16;  /* ALT_NAND_CFG_POR_RST_COUNT_VALUE */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_POR_RST_COUNT. */
typedef volatile struct ALT_NAND_CFG_POR_RST_COUNT_s  ALT_NAND_CFG_POR_RST_COUNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_POR_RST_COUNT register from the beginning of the component. */
#define ALT_NAND_CFG_POR_RST_COUNT_OFST        0x2a0

/*
 * Register : watchdog_reset_count
 * 
 * The number of cycles the controller waits before flagging a watchdog timeout
 * interrupt.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset  | Description                    
 * :--------|:-------|:-------|:--------------------------------
 *  [15:0]  | RW     | 0x5b9a | ALT_NAND_CFG_WD_RST_COUNT_VALUE
 *  [31:16] | ???    | 0x0    | *UNDEFINED*                    
 * 
 */
/*
 * Field : value
 * 
 * The controller waits for this number of cycles before issuing a watchdog timeout
 * interrupt. The value in this register is multiplied internally by 32 in the
 * controller to form the final watchdog counter.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_CFG_WD_RST_COUNT_VALUE register field. */
#define ALT_NAND_CFG_WD_RST_COUNT_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_CFG_WD_RST_COUNT_VALUE register field. */
#define ALT_NAND_CFG_WD_RST_COUNT_VALUE_MSB        15
/* The width in bits of the ALT_NAND_CFG_WD_RST_COUNT_VALUE register field. */
#define ALT_NAND_CFG_WD_RST_COUNT_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_CFG_WD_RST_COUNT_VALUE register field value. */
#define ALT_NAND_CFG_WD_RST_COUNT_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_CFG_WD_RST_COUNT_VALUE register field value. */
#define ALT_NAND_CFG_WD_RST_COUNT_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_CFG_WD_RST_COUNT_VALUE register field. */
#define ALT_NAND_CFG_WD_RST_COUNT_VALUE_RESET      0x5b9a
/* Extracts the ALT_NAND_CFG_WD_RST_COUNT_VALUE field value from a register. */
#define ALT_NAND_CFG_WD_RST_COUNT_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_CFG_WD_RST_COUNT_VALUE register field value suitable for setting the register. */
#define ALT_NAND_CFG_WD_RST_COUNT_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_CFG_WD_RST_COUNT.
 */
struct ALT_NAND_CFG_WD_RST_COUNT_s
{
    uint32_t  value : 16;  /* ALT_NAND_CFG_WD_RST_COUNT_VALUE */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_CFG_WD_RST_COUNT. */
typedef volatile struct ALT_NAND_CFG_WD_RST_COUNT_s  ALT_NAND_CFG_WD_RST_COUNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_CFG_WD_RST_COUNT register from the beginning of the component. */
#define ALT_NAND_CFG_WD_RST_COUNT_OFST        0x2b0

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_NAND_CFG.
 */
struct ALT_NAND_CFG_s
{
    volatile ALT_NAND_CFG_DEVICE_RST_t                 device_reset;               /* ALT_NAND_CFG_DEVICE_RST */
    volatile uint32_t                                  _pad_0x4_0xf[3];            /* *UNDEFINED* */
    volatile ALT_NAND_CFG_TFR_SPARE_REG_t              transfer_spare_reg;         /* ALT_NAND_CFG_TFR_SPARE_REG */
    volatile uint32_t                                  _pad_0x14_0x1f[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_LD_WAIT_CNT_t                load_wait_cnt;              /* ALT_NAND_CFG_LD_WAIT_CNT */
    volatile uint32_t                                  _pad_0x24_0x2f[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_PROGRAM_WAIT_CNT_t           program_wait_cnt;           /* ALT_NAND_CFG_PROGRAM_WAIT_CNT */
    volatile uint32_t                                  _pad_0x34_0x3f[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_ERASE_WAIT_CNT_t             erase_wait_cnt;             /* ALT_NAND_CFG_ERASE_WAIT_CNT */
    volatile uint32_t                                  _pad_0x44_0x4f[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_INT_MON_CYCCNT_t             int_mon_cyccnt;             /* ALT_NAND_CFG_INT_MON_CYCCNT */
    volatile uint32_t                                  _pad_0x54_0x5f[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_RB_PIN_END_t                 rb_pin_enabled;             /* ALT_NAND_CFG_RB_PIN_END */
    volatile uint32_t                                  _pad_0x64_0x6f[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_MULTIPLANE_OP_t              multiplane_operation;       /* ALT_NAND_CFG_MULTIPLANE_OP */
    volatile uint32_t                                  _pad_0x74_0x7f[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_MULTIPLANE_RD_EN_t           multiplane_read_enable;     /* ALT_NAND_CFG_MULTIPLANE_RD_EN */
    volatile uint32_t                                  _pad_0x84_0x8f[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_COPYBACK_DIS_t               copyback_disable;           /* ALT_NAND_CFG_COPYBACK_DIS */
    volatile uint32_t                                  _pad_0x94_0x9f[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_CACHE_WR_EN_t                cache_write_enable;         /* ALT_NAND_CFG_CACHE_WR_EN */
    volatile uint32_t                                  _pad_0xa4_0xaf[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_CACHE_RD_EN_t                cache_read_enable;          /* ALT_NAND_CFG_CACHE_RD_EN */
    volatile uint32_t                                  _pad_0xb4_0xbf[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_PREFETCH_MOD_t               prefetch_mode;              /* ALT_NAND_CFG_PREFETCH_MOD */
    volatile uint32_t                                  _pad_0xc4_0xcf[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_CHIP_EN_DONT_CARE_t          chip_enable_dont_care;      /* ALT_NAND_CFG_CHIP_EN_DONT_CARE */
    volatile uint32_t                                  _pad_0xd4_0xdf[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_ECC_EN_t                     ecc_enable;                 /* ALT_NAND_CFG_ECC_EN */
    volatile uint32_t                                  _pad_0xe4_0xef[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_GLOB_INT_EN_t                global_int_enable;          /* ALT_NAND_CFG_GLOB_INT_EN */
    volatile uint32_t                                  _pad_0xf4_0xff[3];          /* *UNDEFINED* */
    volatile ALT_NAND_CFG_TWHR2_AND_WE_2_RE_t          twhr2_and_we_2_re;          /* ALT_NAND_CFG_TWHR2_AND_WE_2_RE */
    volatile uint32_t                                  _pad_0x104_0x10f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA_t      tcwaw_and_addr_2_data;      /* ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA */
    volatile uint32_t                                  _pad_0x114_0x11f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_RE_2_WE_t                    re_2_we;                    /* ALT_NAND_CFG_RE_2_WE */
    volatile uint32_t                                  _pad_0x124_0x12f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_ACC_CLKS_t                   acc_clks;                   /* ALT_NAND_CFG_ACC_CLKS */
    volatile uint32_t                                  _pad_0x134_0x13f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_NUMBER_OF_PLANES_t           number_of_planes;           /* ALT_NAND_CFG_NUMBER_OF_PLANES */
    volatile uint32_t                                  _pad_0x144_0x14f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_PAGES_PER_BLOCK_t            pages_per_block;            /* ALT_NAND_CFG_PAGES_PER_BLOCK */
    volatile uint32_t                                  _pad_0x154_0x15f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_DEVICE_WIDTH_t               device_width;               /* ALT_NAND_CFG_DEVICE_WIDTH */
    volatile uint32_t                                  _pad_0x164_0x16f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE_t      device_main_area_size;      /* ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE */
    volatile uint32_t                                  _pad_0x174_0x17f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE_t     device_spare_area_size;     /* ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE */
    volatile uint32_t                                  _pad_0x184_0x18f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES_t        two_row_addr_cycles;        /* ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES */
    volatile uint32_t                                  _pad_0x194_0x19f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT_t   multiplane_addr_restrict;   /* ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT */
    volatile uint32_t                                  _pad_0x1a4_0x1af[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_ECC_CORRECTION_t             ecc_correction;             /* ALT_NAND_CFG_ECC_CORRECTION */
    volatile uint32_t                                  _pad_0x1b4_0x1bf[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_RD_MOD_t                     read_mode;                  /* ALT_NAND_CFG_RD_MOD */
    volatile uint32_t                                  _pad_0x1c4_0x1cf[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_WR_MOD_t                     write_mode;                 /* ALT_NAND_CFG_WR_MOD */
    volatile uint32_t                                  _pad_0x1d4_0x1df[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_COPYBACK_MOD_t               copyback_mode;              /* ALT_NAND_CFG_COPYBACK_MOD */
    volatile uint32_t                                  _pad_0x1e4_0x1ef[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_RDWR_EN_LO_CNT_t             rdwr_en_lo_cnt;             /* ALT_NAND_CFG_RDWR_EN_LO_CNT */
    volatile uint32_t                                  _pad_0x1f4_0x1ff[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_RDWR_EN_HI_CNT_t             rdwr_en_hi_cnt;             /* ALT_NAND_CFG_RDWR_EN_HI_CNT */
    volatile uint32_t                                  _pad_0x204_0x20f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_MAX_RD_DELAY_t               max_rd_delay;               /* ALT_NAND_CFG_MAX_RD_DELAY */
    volatile uint32_t                                  _pad_0x214_0x21f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_CS_SETUP_CNT_t               cs_setup_cnt;               /* ALT_NAND_CFG_CS_SETUP_CNT */
    volatile uint32_t                                  _pad_0x224_0x22f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES_t      spare_area_skip_bytes;      /* ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES */
    volatile uint32_t                                  _pad_0x234_0x23f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_SPARE_AREA_MARKER_t          spare_area_marker;          /* ALT_NAND_CFG_SPARE_AREA_MARKER */
    volatile uint32_t                                  _pad_0x244_0x24f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_DEVICES_CONNECTED_t          devices_connected;          /* ALT_NAND_CFG_DEVICES_CONNECTED */
    volatile uint32_t                                  _pad_0x254_0x25f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_DIE_MSK_t                    die_mask;                   /* ALT_NAND_CFG_DIE_MSK */
    volatile uint32_t                                  _pad_0x264_0x26f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE_t  first_block_of_next_plane;  /* ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE */
    volatile uint32_t                                  _pad_0x274_0x27f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_WR_PROTECT_t                 write_protect;              /* ALT_NAND_CFG_WR_PROTECT */
    volatile uint32_t                                  _pad_0x284_0x28f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_RE_2_RE_t                    re_2_re;                    /* ALT_NAND_CFG_RE_2_RE */
    volatile uint32_t                                  _pad_0x294_0x29f[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_POR_RST_COUNT_t              por_reset_count;            /* ALT_NAND_CFG_POR_RST_COUNT */
    volatile uint32_t                                  _pad_0x2a4_0x2af[3];        /* *UNDEFINED* */
    volatile ALT_NAND_CFG_WD_RST_COUNT_t               watchdog_reset_count;       /* ALT_NAND_CFG_WD_RST_COUNT */
};

/* The typedef declaration for register group ALT_NAND_CFG. */
typedef volatile struct ALT_NAND_CFG_s  ALT_NAND_CFG_t;
/* The struct declaration for the raw register contents of register group ALT_NAND_CFG. */
struct ALT_NAND_CFG_raw_s
{
    volatile uint32_t  device_reset;               /* ALT_NAND_CFG_DEVICE_RST */
    volatile uint32_t  _pad_0x4_0xf[3];            /* *UNDEFINED* */
    volatile uint32_t  transfer_spare_reg;         /* ALT_NAND_CFG_TFR_SPARE_REG */
    volatile uint32_t  _pad_0x14_0x1f[3];          /* *UNDEFINED* */
    volatile uint32_t  load_wait_cnt;              /* ALT_NAND_CFG_LD_WAIT_CNT */
    volatile uint32_t  _pad_0x24_0x2f[3];          /* *UNDEFINED* */
    volatile uint32_t  program_wait_cnt;           /* ALT_NAND_CFG_PROGRAM_WAIT_CNT */
    volatile uint32_t  _pad_0x34_0x3f[3];          /* *UNDEFINED* */
    volatile uint32_t  erase_wait_cnt;             /* ALT_NAND_CFG_ERASE_WAIT_CNT */
    volatile uint32_t  _pad_0x44_0x4f[3];          /* *UNDEFINED* */
    volatile uint32_t  int_mon_cyccnt;             /* ALT_NAND_CFG_INT_MON_CYCCNT */
    volatile uint32_t  _pad_0x54_0x5f[3];          /* *UNDEFINED* */
    volatile uint32_t  rb_pin_enabled;             /* ALT_NAND_CFG_RB_PIN_END */
    volatile uint32_t  _pad_0x64_0x6f[3];          /* *UNDEFINED* */
    volatile uint32_t  multiplane_operation;       /* ALT_NAND_CFG_MULTIPLANE_OP */
    volatile uint32_t  _pad_0x74_0x7f[3];          /* *UNDEFINED* */
    volatile uint32_t  multiplane_read_enable;     /* ALT_NAND_CFG_MULTIPLANE_RD_EN */
    volatile uint32_t  _pad_0x84_0x8f[3];          /* *UNDEFINED* */
    volatile uint32_t  copyback_disable;           /* ALT_NAND_CFG_COPYBACK_DIS */
    volatile uint32_t  _pad_0x94_0x9f[3];          /* *UNDEFINED* */
    volatile uint32_t  cache_write_enable;         /* ALT_NAND_CFG_CACHE_WR_EN */
    volatile uint32_t  _pad_0xa4_0xaf[3];          /* *UNDEFINED* */
    volatile uint32_t  cache_read_enable;          /* ALT_NAND_CFG_CACHE_RD_EN */
    volatile uint32_t  _pad_0xb4_0xbf[3];          /* *UNDEFINED* */
    volatile uint32_t  prefetch_mode;              /* ALT_NAND_CFG_PREFETCH_MOD */
    volatile uint32_t  _pad_0xc4_0xcf[3];          /* *UNDEFINED* */
    volatile uint32_t  chip_enable_dont_care;      /* ALT_NAND_CFG_CHIP_EN_DONT_CARE */
    volatile uint32_t  _pad_0xd4_0xdf[3];          /* *UNDEFINED* */
    volatile uint32_t  ecc_enable;                 /* ALT_NAND_CFG_ECC_EN */
    volatile uint32_t  _pad_0xe4_0xef[3];          /* *UNDEFINED* */
    volatile uint32_t  global_int_enable;          /* ALT_NAND_CFG_GLOB_INT_EN */
    volatile uint32_t  _pad_0xf4_0xff[3];          /* *UNDEFINED* */
    volatile uint32_t  twhr2_and_we_2_re;          /* ALT_NAND_CFG_TWHR2_AND_WE_2_RE */
    volatile uint32_t  _pad_0x104_0x10f[3];        /* *UNDEFINED* */
    volatile uint32_t  tcwaw_and_addr_2_data;      /* ALT_NAND_CFG_TCWAW_AND_ADDR_2_DATA */
    volatile uint32_t  _pad_0x114_0x11f[3];        /* *UNDEFINED* */
    volatile uint32_t  re_2_we;                    /* ALT_NAND_CFG_RE_2_WE */
    volatile uint32_t  _pad_0x124_0x12f[3];        /* *UNDEFINED* */
    volatile uint32_t  acc_clks;                   /* ALT_NAND_CFG_ACC_CLKS */
    volatile uint32_t  _pad_0x134_0x13f[3];        /* *UNDEFINED* */
    volatile uint32_t  number_of_planes;           /* ALT_NAND_CFG_NUMBER_OF_PLANES */
    volatile uint32_t  _pad_0x144_0x14f[3];        /* *UNDEFINED* */
    volatile uint32_t  pages_per_block;            /* ALT_NAND_CFG_PAGES_PER_BLOCK */
    volatile uint32_t  _pad_0x154_0x15f[3];        /* *UNDEFINED* */
    volatile uint32_t  device_width;               /* ALT_NAND_CFG_DEVICE_WIDTH */
    volatile uint32_t  _pad_0x164_0x16f[3];        /* *UNDEFINED* */
    volatile uint32_t  device_main_area_size;      /* ALT_NAND_CFG_DEVICE_MAIN_AREA_SIZE */
    volatile uint32_t  _pad_0x174_0x17f[3];        /* *UNDEFINED* */
    volatile uint32_t  device_spare_area_size;     /* ALT_NAND_CFG_DEVICE_SPARE_AREA_SIZE */
    volatile uint32_t  _pad_0x184_0x18f[3];        /* *UNDEFINED* */
    volatile uint32_t  two_row_addr_cycles;        /* ALT_NAND_CFG_TWO_ROW_ADDR_CYCLES */
    volatile uint32_t  _pad_0x194_0x19f[3];        /* *UNDEFINED* */
    volatile uint32_t  multiplane_addr_restrict;   /* ALT_NAND_CFG_MULTIPLANE_ADDR_RESTRICT */
    volatile uint32_t  _pad_0x1a4_0x1af[3];        /* *UNDEFINED* */
    volatile uint32_t  ecc_correction;             /* ALT_NAND_CFG_ECC_CORRECTION */
    volatile uint32_t  _pad_0x1b4_0x1bf[3];        /* *UNDEFINED* */
    volatile uint32_t  read_mode;                  /* ALT_NAND_CFG_RD_MOD */
    volatile uint32_t  _pad_0x1c4_0x1cf[3];        /* *UNDEFINED* */
    volatile uint32_t  write_mode;                 /* ALT_NAND_CFG_WR_MOD */
    volatile uint32_t  _pad_0x1d4_0x1df[3];        /* *UNDEFINED* */
    volatile uint32_t  copyback_mode;              /* ALT_NAND_CFG_COPYBACK_MOD */
    volatile uint32_t  _pad_0x1e4_0x1ef[3];        /* *UNDEFINED* */
    volatile uint32_t  rdwr_en_lo_cnt;             /* ALT_NAND_CFG_RDWR_EN_LO_CNT */
    volatile uint32_t  _pad_0x1f4_0x1ff[3];        /* *UNDEFINED* */
    volatile uint32_t  rdwr_en_hi_cnt;             /* ALT_NAND_CFG_RDWR_EN_HI_CNT */
    volatile uint32_t  _pad_0x204_0x20f[3];        /* *UNDEFINED* */
    volatile uint32_t  max_rd_delay;               /* ALT_NAND_CFG_MAX_RD_DELAY */
    volatile uint32_t  _pad_0x214_0x21f[3];        /* *UNDEFINED* */
    volatile uint32_t  cs_setup_cnt;               /* ALT_NAND_CFG_CS_SETUP_CNT */
    volatile uint32_t  _pad_0x224_0x22f[3];        /* *UNDEFINED* */
    volatile uint32_t  spare_area_skip_bytes;      /* ALT_NAND_CFG_SPARE_AREA_SKIP_BYTES */
    volatile uint32_t  _pad_0x234_0x23f[3];        /* *UNDEFINED* */
    volatile uint32_t  spare_area_marker;          /* ALT_NAND_CFG_SPARE_AREA_MARKER */
    volatile uint32_t  _pad_0x244_0x24f[3];        /* *UNDEFINED* */
    volatile uint32_t  devices_connected;          /* ALT_NAND_CFG_DEVICES_CONNECTED */
    volatile uint32_t  _pad_0x254_0x25f[3];        /* *UNDEFINED* */
    volatile uint32_t  die_mask;                   /* ALT_NAND_CFG_DIE_MSK */
    volatile uint32_t  _pad_0x264_0x26f[3];        /* *UNDEFINED* */
    volatile uint32_t  first_block_of_next_plane;  /* ALT_NAND_CFG_FIRST_BLOCK_OF_NEXT_PLANE */
    volatile uint32_t  _pad_0x274_0x27f[3];        /* *UNDEFINED* */
    volatile uint32_t  write_protect;              /* ALT_NAND_CFG_WR_PROTECT */
    volatile uint32_t  _pad_0x284_0x28f[3];        /* *UNDEFINED* */
    volatile uint32_t  re_2_re;                    /* ALT_NAND_CFG_RE_2_RE */
    volatile uint32_t  _pad_0x294_0x29f[3];        /* *UNDEFINED* */
    volatile uint32_t  por_reset_count;            /* ALT_NAND_CFG_POR_RST_COUNT */
    volatile uint32_t  _pad_0x2a4_0x2af[3];        /* *UNDEFINED* */
    volatile uint32_t  watchdog_reset_count;       /* ALT_NAND_CFG_WD_RST_COUNT */
};

/* The typedef declaration for the raw register contents of register group ALT_NAND_CFG. */
typedef volatile struct ALT_NAND_CFG_raw_s  ALT_NAND_CFG_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : Device parameters - ALT_NAND_PARAM
 * Device parameters
 * 
 * Controller reads device parameters after initialization and stores in the
 * following registers for software
 * 
 */
/*
 * Register : manufacturer_id
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                         
 * :-------|:-------|:------|:-------------------------------------
 *  [7:0]  | RW     | 0x0   | ALT_NAND_PARAM_MANUFACTURER_ID_VALUE
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                         
 * 
 */
/*
 * Field : value
 * 
 * Manufacturer ID
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_MANUFACTURER_ID_VALUE register field. */
#define ALT_NAND_PARAM_MANUFACTURER_ID_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_MANUFACTURER_ID_VALUE register field. */
#define ALT_NAND_PARAM_MANUFACTURER_ID_VALUE_MSB        7
/* The width in bits of the ALT_NAND_PARAM_MANUFACTURER_ID_VALUE register field. */
#define ALT_NAND_PARAM_MANUFACTURER_ID_VALUE_WIDTH      8
/* The mask used to set the ALT_NAND_PARAM_MANUFACTURER_ID_VALUE register field value. */
#define ALT_NAND_PARAM_MANUFACTURER_ID_VALUE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_NAND_PARAM_MANUFACTURER_ID_VALUE register field value. */
#define ALT_NAND_PARAM_MANUFACTURER_ID_VALUE_CLR_MSK    0xffffff00
/* The reset value of the ALT_NAND_PARAM_MANUFACTURER_ID_VALUE register field. */
#define ALT_NAND_PARAM_MANUFACTURER_ID_VALUE_RESET      0x0
/* Extracts the ALT_NAND_PARAM_MANUFACTURER_ID_VALUE field value from a register. */
#define ALT_NAND_PARAM_MANUFACTURER_ID_VALUE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_NAND_PARAM_MANUFACTURER_ID_VALUE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_MANUFACTURER_ID_VALUE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_MANUFACTURER_ID.
 */
struct ALT_NAND_PARAM_MANUFACTURER_ID_s
{
    uint32_t  value :  8;  /* ALT_NAND_PARAM_MANUFACTURER_ID_VALUE */
    uint32_t        : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_MANUFACTURER_ID. */
typedef volatile struct ALT_NAND_PARAM_MANUFACTURER_ID_s  ALT_NAND_PARAM_MANUFACTURER_ID_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_MANUFACTURER_ID register from the beginning of the component. */
#define ALT_NAND_PARAM_MANUFACTURER_ID_OFST        0x0

/*
 * Register : device_id
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                   
 * :-------|:-------|:------|:-------------------------------
 *  [7:0]  | R      | 0x0   | ALT_NAND_PARAM_DEVICE_ID_VALUE
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                   
 * 
 */
/*
 * Field : value
 * 
 * Device ID. This register is updated only for Legacy NAND devices.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_DEVICE_ID_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_ID_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_DEVICE_ID_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_ID_VALUE_MSB        7
/* The width in bits of the ALT_NAND_PARAM_DEVICE_ID_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_ID_VALUE_WIDTH      8
/* The mask used to set the ALT_NAND_PARAM_DEVICE_ID_VALUE register field value. */
#define ALT_NAND_PARAM_DEVICE_ID_VALUE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_NAND_PARAM_DEVICE_ID_VALUE register field value. */
#define ALT_NAND_PARAM_DEVICE_ID_VALUE_CLR_MSK    0xffffff00
/* The reset value of the ALT_NAND_PARAM_DEVICE_ID_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_ID_VALUE_RESET      0x0
/* Extracts the ALT_NAND_PARAM_DEVICE_ID_VALUE field value from a register. */
#define ALT_NAND_PARAM_DEVICE_ID_VALUE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_NAND_PARAM_DEVICE_ID_VALUE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_DEVICE_ID_VALUE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_DEVICE_ID.
 */
struct ALT_NAND_PARAM_DEVICE_ID_s
{
    const uint32_t  value :  8;  /* ALT_NAND_PARAM_DEVICE_ID_VALUE */
    uint32_t              : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_DEVICE_ID. */
typedef volatile struct ALT_NAND_PARAM_DEVICE_ID_s  ALT_NAND_PARAM_DEVICE_ID_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_DEVICE_ID register from the beginning of the component. */
#define ALT_NAND_PARAM_DEVICE_ID_OFST        0x10

/*
 * Register : device_param_0
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                        
 * :-------|:-------|:------|:------------------------------------
 *  [7:0]  | R      | 0x0   | ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : value
 * 
 * 3rd byte relating to Device Signature. This register is updated only for Legacy
 * NAND devices.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE_MSB        7
/* The width in bits of the ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE_WIDTH      8
/* The mask used to set the ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE register field value. */
#define ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE register field value. */
#define ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE_CLR_MSK    0xffffff00
/* The reset value of the ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE_RESET      0x0
/* Extracts the ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE field value from a register. */
#define ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_DEVICE_PARAM_0.
 */
struct ALT_NAND_PARAM_DEVICE_PARAM_0_s
{
    const uint32_t  value :  8;  /* ALT_NAND_PARAM_DEVICE_PARAM_0_VALUE */
    uint32_t              : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_DEVICE_PARAM_0. */
typedef volatile struct ALT_NAND_PARAM_DEVICE_PARAM_0_s  ALT_NAND_PARAM_DEVICE_PARAM_0_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_DEVICE_PARAM_0 register from the beginning of the component. */
#define ALT_NAND_PARAM_DEVICE_PARAM_0_OFST        0x20

/*
 * Register : device_param_1
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                        
 * :-------|:-------|:------|:------------------------------------
 *  [7:0]  | R      | 0x0   | ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : value
 * 
 * 4th byte relating to Device Signature. This register is updated only for Legacy
 * NAND devices.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE_MSB        7
/* The width in bits of the ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE_WIDTH      8
/* The mask used to set the ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE register field value. */
#define ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE register field value. */
#define ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE_CLR_MSK    0xffffff00
/* The reset value of the ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE_RESET      0x0
/* Extracts the ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE field value from a register. */
#define ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_DEVICE_PARAM_1.
 */
struct ALT_NAND_PARAM_DEVICE_PARAM_1_s
{
    const uint32_t  value :  8;  /* ALT_NAND_PARAM_DEVICE_PARAM_1_VALUE */
    uint32_t              : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_DEVICE_PARAM_1. */
typedef volatile struct ALT_NAND_PARAM_DEVICE_PARAM_1_s  ALT_NAND_PARAM_DEVICE_PARAM_1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_DEVICE_PARAM_1 register from the beginning of the component. */
#define ALT_NAND_PARAM_DEVICE_PARAM_1_OFST        0x30

/*
 * Register : device_param_2
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                        
 * :-------|:-------|:------|:------------------------------------
 *  [7:0]  | R      | 0x0   | ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : value
 * 
 * Reserved.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE_MSB        7
/* The width in bits of the ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE_WIDTH      8
/* The mask used to set the ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE register field value. */
#define ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE register field value. */
#define ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE_CLR_MSK    0xffffff00
/* The reset value of the ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE register field. */
#define ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE_RESET      0x0
/* Extracts the ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE field value from a register. */
#define ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_DEVICE_PARAM_2.
 */
struct ALT_NAND_PARAM_DEVICE_PARAM_2_s
{
    const uint32_t  value :  8;  /* ALT_NAND_PARAM_DEVICE_PARAM_2_VALUE */
    uint32_t              : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_DEVICE_PARAM_2. */
typedef volatile struct ALT_NAND_PARAM_DEVICE_PARAM_2_s  ALT_NAND_PARAM_DEVICE_PARAM_2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_DEVICE_PARAM_2 register from the beginning of the component. */
#define ALT_NAND_PARAM_DEVICE_PARAM_2_OFST        0x40

/*
 * Register : logical_page_data_size
 * 
 * Logical page data area size in bytes
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                
 * :--------|:-------|:------|:--------------------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                                
 * 
 */
/*
 * Field : value
 * 
 * Logical page spare area size in bytes. If multiple devices are connected on a
 * single chip select, physical page data size will be multiplied by the number of
 * devices to arrive at logical page size.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE register field. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE register field. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE_MSB        15
/* The width in bits of the ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE register field. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE register field value. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE register field value. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE register field. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE_RESET      0x0
/* Extracts the ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE field value from a register. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE.
 */
struct ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_s
{
    const uint32_t  value : 16;  /* ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE. */
typedef volatile struct ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_s  ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE register from the beginning of the component. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_OFST        0x50

/*
 * Register : logical_page_spare_size
 * 
 * Logical page data area size in bytes
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                 
 * :--------|:-------|:------|:---------------------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                                 
 * 
 */
/*
 * Field : value
 * 
 * Logical page spare area size in bytes. If multiple devices are connected on a
 * single chip select, physical page spare size will be multiplied by the number of
 * devices to arrive at logical page size.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE register field. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE register field. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE_MSB        15
/* The width in bits of the ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE register field. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE register field value. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE register field value. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE register field. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE_RESET      0x0
/* Extracts the ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE field value from a register. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE.
 */
struct ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_s
{
    const uint32_t  value : 16;  /* ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE. */
typedef volatile struct ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_s  ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE register from the beginning of the component. */
#define ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_OFST        0x60

/*
 * Register : revision
 * 
 * Controller revision number
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                  
 * :--------|:-------|:------|:------------------------------
 *  [15:0]  | R      | 0x5   | ALT_NAND_PARAM_REVISION_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : value
 * 
 * Controller revision number
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_REVISION_VALUE register field. */
#define ALT_NAND_PARAM_REVISION_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_REVISION_VALUE register field. */
#define ALT_NAND_PARAM_REVISION_VALUE_MSB        15
/* The width in bits of the ALT_NAND_PARAM_REVISION_VALUE register field. */
#define ALT_NAND_PARAM_REVISION_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_PARAM_REVISION_VALUE register field value. */
#define ALT_NAND_PARAM_REVISION_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_PARAM_REVISION_VALUE register field value. */
#define ALT_NAND_PARAM_REVISION_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_PARAM_REVISION_VALUE register field. */
#define ALT_NAND_PARAM_REVISION_VALUE_RESET      0x5
/* Extracts the ALT_NAND_PARAM_REVISION_VALUE field value from a register. */
#define ALT_NAND_PARAM_REVISION_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_PARAM_REVISION_VALUE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_REVISION_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_REVISION.
 */
struct ALT_NAND_PARAM_REVISION_s
{
    const uint32_t  value : 16;  /* ALT_NAND_PARAM_REVISION_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_REVISION. */
typedef volatile struct ALT_NAND_PARAM_REVISION_s  ALT_NAND_PARAM_REVISION_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_REVISION register from the beginning of the component. */
#define ALT_NAND_PARAM_REVISION_OFST        0x70

/*
 * Register : onfi_device_features
 * 
 * Features supported by the connected ONFI device
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                           
 * :--------|:-------|:------|:---------------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                           
 * 
 */
/*
 * Field : value
 * 
 * The values in the field should be interpreted as follows[list] [*]Bit 0 -
 * Supports 16 bit data bus width. [*]Bit 1 - Supports multiple LUN operations.
 * [*]Bit 2 - Supports non-sequential page programming. [*]Bit 3 - Supports
 * interleaved program and erase operations. [*]Bit 4 - Supports odd to even page
 * copyback. [*]Bit 5 - Supports source synchronous. [*]Bit 6 - Supports
 * interleaved read operations. [*]Bit 7 - Supports extended parameter page. [*]Bit
 * 8 - Supports program page register clear enhancement. [*]Bit 9-15 -
 * Reserved.[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE_MSB        15
/* The width in bits of the ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE register field value. */
#define ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE register field value. */
#define ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE_RESET      0x0
/* Extracts the ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE field value from a register. */
#define ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_ONFI_DEV_FEATURES.
 */
struct ALT_NAND_PARAM_ONFI_DEV_FEATURES_s
{
    const uint32_t  value : 16;  /* ALT_NAND_PARAM_ONFI_DEV_FEATURES_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_ONFI_DEV_FEATURES. */
typedef volatile struct ALT_NAND_PARAM_ONFI_DEV_FEATURES_s  ALT_NAND_PARAM_ONFI_DEV_FEATURES_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_ONFI_DEV_FEATURES register from the beginning of the component. */
#define ALT_NAND_PARAM_ONFI_DEV_FEATURES_OFST        0x80

/*
 * Register : onfi_optional_commands
 * 
 * Optional commands supported by the connected ONFI device
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                            
 * :--------|:-------|:------|:----------------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                            
 * 
 */
/*
 * Field : value
 * 
 * The values in the field should be interpreted as follows[list] [*]Bit 0 -
 * Supports page cache program command. [*]Bit 1 - Supports read cache commands.
 * [*]Bit 2 - Supports get and set features. [*]Bit 3 - Supports read status
 * enhanced commands. [*]Bit 4 - Supports copyback. [*]Bit 5 - Supports Read Unique
 * Id. [*]Bit 6 - Supports Change Read Column Enhanced. [*]Bit 7 - Supports change
 * row address. [*]Bit 8 - Supports Change small data move. [*]Bit 9 - Supports
 * RESET Lun. [*]Bit 10-15 - Reserved.[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE_MSB        15
/* The width in bits of the ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE register field value. */
#define ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE register field value. */
#define ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE_RESET      0x0
/* Extracts the ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE field value from a register. */
#define ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS.
 */
struct ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_s
{
    const uint32_t  value : 16;  /* ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS. */
typedef volatile struct ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_s  ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS register from the beginning of the component. */
#define ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_OFST        0x90

/*
 * Register : onfi_timing_mode
 * 
 * Asynchronous Timing modes supported by the connected ONFI device
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                         
 * :-------|:-------|:------|:-------------------------------------
 *  [5:0]  | R      | 0x0   | ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE
 *  [31:6] | ???    | 0x0   | *UNDEFINED*                         
 * 
 */
/*
 * Field : value
 * 
 * The values in the field should be interpreted as follows[list] [*]Bit 0 -
 * Supports Timing mode 0. [*]Bit 1 - Supports Timing mode 1. [*]Bit 2 - Supports
 * Timing mode 2. [*]Bit 3 - Supports Timing mode 3. [*]Bit 4 - Supports Timing
 * mode 4. [*]Bit 5 - Supports Timing mode 5.[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE_MSB        5
/* The width in bits of the ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE_WIDTH      6
/* The mask used to set the ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE register field value. */
#define ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE_SET_MSK    0x0000003f
/* The mask used to clear the ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE register field value. */
#define ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE_CLR_MSK    0xffffffc0
/* The reset value of the ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE_RESET      0x0
/* Extracts the ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE field value from a register. */
#define ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE_GET(value) (((value) & 0x0000003f) >> 0)
/* Produces a ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE_SET(value) (((value) << 0) & 0x0000003f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_ONFI_TIMING_MOD.
 */
struct ALT_NAND_PARAM_ONFI_TIMING_MOD_s
{
    const uint32_t  value :  6;  /* ALT_NAND_PARAM_ONFI_TIMING_MOD_VALUE */
    uint32_t              : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_ONFI_TIMING_MOD. */
typedef volatile struct ALT_NAND_PARAM_ONFI_TIMING_MOD_s  ALT_NAND_PARAM_ONFI_TIMING_MOD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_ONFI_TIMING_MOD register from the beginning of the component. */
#define ALT_NAND_PARAM_ONFI_TIMING_MOD_OFST        0xa0

/*
 * Register : onfi_pgm_cache_timing_mode
 * 
 * Asynchronous Program Cache Timing modes supported by the connected ONFI device
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                                   
 * :-------|:-------|:------|:-----------------------------------------------
 *  [5:0]  | R      | 0x0   | ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE
 *  [31:6] | ???    | 0x0   | *UNDEFINED*                                   
 * 
 */
/*
 * Field : value
 * 
 * The values in the field should be interpreted as follows[list] [*]Bit 0 -
 * Supports Timing mode 0. [*]Bit 1 - Supports Timing mode 1. [*]Bit 2 - Supports
 * Timing mode 2. [*]Bit 3 - Supports Timing mode 3. [*]Bit 4 - Supports Timing
 * mode 4. [*]Bit 5 - Supports Timing mode 5.[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE_MSB        5
/* The width in bits of the ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE_WIDTH      6
/* The mask used to set the ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE register field value. */
#define ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE_SET_MSK    0x0000003f
/* The mask used to clear the ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE register field value. */
#define ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE_CLR_MSK    0xffffffc0
/* The reset value of the ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE_RESET      0x0
/* Extracts the ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE field value from a register. */
#define ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE_GET(value) (((value) & 0x0000003f) >> 0)
/* Produces a ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE_SET(value) (((value) << 0) & 0x0000003f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD.
 */
struct ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_s
{
    const uint32_t  value :  6;  /* ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_VALUE */
    uint32_t              : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD. */
typedef volatile struct ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_s  ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD register from the beginning of the component. */
#define ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_OFST        0xb0

/*
 * Register : onfi_device_no_of_luns
 * 
 * Indicates if the device is an ONFI compliant device and the number of LUNS
 * present in the device
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                                   
 * :-------|:-------|:------|:-----------------------------------------------
 *  [7:0]  | R      | 0x0   | ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS 
 *  [8]    | RW     | 0x0   | ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE
 *  [31:9] | ???    | 0x0   | *UNDEFINED*                                   
 * 
 */
/*
 * Field : no_of_luns
 * 
 * Indicates the number of LUNS present in the device
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS register field. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS register field. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS_MSB        7
/* The width in bits of the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS register field. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS_WIDTH      8
/* The mask used to set the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS register field value. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS_SET_MSK    0x000000ff
/* The mask used to clear the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS register field value. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS_CLR_MSK    0xffffff00
/* The reset value of the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS register field. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS_RESET      0x0
/* Extracts the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS field value from a register. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS register field value suitable for setting the register. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS_SET(value) (((value) << 0) & 0x000000ff)

/*
 * Field : onfi_device
 * 
 * Indicates if the device is an ONFI compliant device.[list] [*]0 - Non-ONFI
 * compliant device [*]1 - ONFI compliant device[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE_MSB        8
/* The width in bits of the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE_WIDTH      1
/* The mask used to set the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE register field value. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE_SET_MSK    0x00000100
/* The mask used to clear the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE register field value. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE_CLR_MSK    0xfffffeff
/* The reset value of the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE_RESET      0x0
/* Extracts the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE field value from a register. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE_SET(value) (((value) << 8) & 0x00000100)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS.
 */
struct ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_s
{
    const uint32_t  no_of_luns  :  8;  /* ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_NO_OF_LUNS */
    uint32_t        onfi_device :  1;  /* ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_ONFI_DEVICE */
    uint32_t                    : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS. */
typedef volatile struct ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_s  ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS register from the beginning of the component. */
#define ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_OFST        0xc0

/*
 * Register : onfi_device_no_of_blocks_per_lun_l
 * 
 * Lower bits of number of blocks per LUN present in the ONFI complaint device.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                 
 * :--------|:-------|:------|:---------------------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                                 
 * 
 */
/*
 * Field : value
 * 
 * Indicates the lower bits of number of blocks per LUN present in the ONFI
 * complaint device.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE_MSB        15
/* The width in bits of the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE register field value. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE register field value. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE_RESET      0x0
/* Extracts the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE field value from a register. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L.
 */
struct ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_s
{
    const uint32_t  value : 16;  /* ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L. */
typedef volatile struct ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_s  ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L register from the beginning of the component. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_OFST        0xd0

/*
 * Register : onfi_device_no_of_blocks_per_lun_u
 * 
 * Upper bits of number of blocks per LUN present in the ONFI complaint device.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                 
 * :--------|:-------|:------|:---------------------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                                 
 * 
 */
/*
 * Field : value
 * 
 * Indicates the upper bits of number of blocks per LUN present in the ONFI
 * complaint device.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE_MSB        15
/* The width in bits of the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE register field value. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE register field value. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE register field. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE_RESET      0x0
/* Extracts the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE field value from a register. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE register field value suitable for setting the register. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U.
 */
struct ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_s
{
    const uint32_t  value : 16;  /* ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U. */
typedef volatile struct ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_s  ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U register from the beginning of the component. */
#define ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_OFST        0xe0

/*
 * Register : features
 * 
 * Shows Available hardware features or attributes
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                          
 * :--------|:-------|:------|:--------------------------------------
 *  [1:0]   | R      | 0x1   | ALT_NAND_PARAM_FEATURES_N_BANKS      
 *  [5:2]   | ???    | 0x0   | *UNDEFINED*                          
 *  [6]     | R      | 0x1   | ALT_NAND_PARAM_FEATURES_DMA          
 *  [7]     | R      | 0x0   | ALT_NAND_PARAM_FEATURES_CMD_DMA      
 *  [8]     | R      | 0x0   | ALT_NAND_PARAM_FEATURES_PARTITION    
 *  [9]     | R      | 0x0   | ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND
 *  [10]    | R      | 0x0   | ALT_NAND_PARAM_FEATURES_GPREG        
 *  [11]    | R      | 0x1   | ALT_NAND_PARAM_FEATURES_INDEX_ADDR   
 *  [12]    | R      | 0x0   | ALT_NAND_PARAM_FEATURES_DFI_INTF     
 *  [13]    | R      | 0x0   | ALT_NAND_PARAM_FEATURES_LBA          
 *  [31:14] | ???    | 0x0   | *UNDEFINED*                          
 * 
 */
/*
 * Field : n_banks
 * 
 * Maximum number of banks supported by hardware. This is an encoded value.
 * [list][*]0 - Two banks [*]1 - Four banks [*]2 - Eight banks [*]3 - Sixteen
 * banks[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_FEATURES_N_BANKS register field. */
#define ALT_NAND_PARAM_FEATURES_N_BANKS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_FEATURES_N_BANKS register field. */
#define ALT_NAND_PARAM_FEATURES_N_BANKS_MSB        1
/* The width in bits of the ALT_NAND_PARAM_FEATURES_N_BANKS register field. */
#define ALT_NAND_PARAM_FEATURES_N_BANKS_WIDTH      2
/* The mask used to set the ALT_NAND_PARAM_FEATURES_N_BANKS register field value. */
#define ALT_NAND_PARAM_FEATURES_N_BANKS_SET_MSK    0x00000003
/* The mask used to clear the ALT_NAND_PARAM_FEATURES_N_BANKS register field value. */
#define ALT_NAND_PARAM_FEATURES_N_BANKS_CLR_MSK    0xfffffffc
/* The reset value of the ALT_NAND_PARAM_FEATURES_N_BANKS register field. */
#define ALT_NAND_PARAM_FEATURES_N_BANKS_RESET      0x1
/* Extracts the ALT_NAND_PARAM_FEATURES_N_BANKS field value from a register. */
#define ALT_NAND_PARAM_FEATURES_N_BANKS_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_NAND_PARAM_FEATURES_N_BANKS register field value suitable for setting the register. */
#define ALT_NAND_PARAM_FEATURES_N_BANKS_SET(value) (((value) << 0) & 0x00000003)

/*
 * Field : dma
 * 
 * if set, DATA-DMA is present in hardware.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_FEATURES_DMA register field. */
#define ALT_NAND_PARAM_FEATURES_DMA_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_FEATURES_DMA register field. */
#define ALT_NAND_PARAM_FEATURES_DMA_MSB        6
/* The width in bits of the ALT_NAND_PARAM_FEATURES_DMA register field. */
#define ALT_NAND_PARAM_FEATURES_DMA_WIDTH      1
/* The mask used to set the ALT_NAND_PARAM_FEATURES_DMA register field value. */
#define ALT_NAND_PARAM_FEATURES_DMA_SET_MSK    0x00000040
/* The mask used to clear the ALT_NAND_PARAM_FEATURES_DMA register field value. */
#define ALT_NAND_PARAM_FEATURES_DMA_CLR_MSK    0xffffffbf
/* The reset value of the ALT_NAND_PARAM_FEATURES_DMA register field. */
#define ALT_NAND_PARAM_FEATURES_DMA_RESET      0x1
/* Extracts the ALT_NAND_PARAM_FEATURES_DMA field value from a register. */
#define ALT_NAND_PARAM_FEATURES_DMA_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_NAND_PARAM_FEATURES_DMA register field value suitable for setting the register. */
#define ALT_NAND_PARAM_FEATURES_DMA_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : cmd_dma
 * 
 * Not implemented.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_FEATURES_CMD_DMA register field. */
#define ALT_NAND_PARAM_FEATURES_CMD_DMA_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_FEATURES_CMD_DMA register field. */
#define ALT_NAND_PARAM_FEATURES_CMD_DMA_MSB        7
/* The width in bits of the ALT_NAND_PARAM_FEATURES_CMD_DMA register field. */
#define ALT_NAND_PARAM_FEATURES_CMD_DMA_WIDTH      1
/* The mask used to set the ALT_NAND_PARAM_FEATURES_CMD_DMA register field value. */
#define ALT_NAND_PARAM_FEATURES_CMD_DMA_SET_MSK    0x00000080
/* The mask used to clear the ALT_NAND_PARAM_FEATURES_CMD_DMA register field value. */
#define ALT_NAND_PARAM_FEATURES_CMD_DMA_CLR_MSK    0xffffff7f
/* The reset value of the ALT_NAND_PARAM_FEATURES_CMD_DMA register field. */
#define ALT_NAND_PARAM_FEATURES_CMD_DMA_RESET      0x0
/* Extracts the ALT_NAND_PARAM_FEATURES_CMD_DMA field value from a register. */
#define ALT_NAND_PARAM_FEATURES_CMD_DMA_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_NAND_PARAM_FEATURES_CMD_DMA register field value suitable for setting the register. */
#define ALT_NAND_PARAM_FEATURES_CMD_DMA_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : partition
 * 
 * if set, Partition logic is present in hardware.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_FEATURES_PARTITION register field. */
#define ALT_NAND_PARAM_FEATURES_PARTITION_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_FEATURES_PARTITION register field. */
#define ALT_NAND_PARAM_FEATURES_PARTITION_MSB        8
/* The width in bits of the ALT_NAND_PARAM_FEATURES_PARTITION register field. */
#define ALT_NAND_PARAM_FEATURES_PARTITION_WIDTH      1
/* The mask used to set the ALT_NAND_PARAM_FEATURES_PARTITION register field value. */
#define ALT_NAND_PARAM_FEATURES_PARTITION_SET_MSK    0x00000100
/* The mask used to clear the ALT_NAND_PARAM_FEATURES_PARTITION register field value. */
#define ALT_NAND_PARAM_FEATURES_PARTITION_CLR_MSK    0xfffffeff
/* The reset value of the ALT_NAND_PARAM_FEATURES_PARTITION register field. */
#define ALT_NAND_PARAM_FEATURES_PARTITION_RESET      0x0
/* Extracts the ALT_NAND_PARAM_FEATURES_PARTITION field value from a register. */
#define ALT_NAND_PARAM_FEATURES_PARTITION_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_NAND_PARAM_FEATURES_PARTITION register field value suitable for setting the register. */
#define ALT_NAND_PARAM_FEATURES_PARTITION_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : xdma_sideband
 * 
 * if set, Side band DMA signals are present in hardware.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND register field. */
#define ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND register field. */
#define ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND_MSB        9
/* The width in bits of the ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND register field. */
#define ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND_WIDTH      1
/* The mask used to set the ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND register field value. */
#define ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND_SET_MSK    0x00000200
/* The mask used to clear the ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND register field value. */
#define ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND_CLR_MSK    0xfffffdff
/* The reset value of the ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND register field. */
#define ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND_RESET      0x0
/* Extracts the ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND field value from a register. */
#define ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND register field value suitable for setting the register. */
#define ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : gpreg
 * 
 * if set, General purpose registers are is present in hardware.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_FEATURES_GPREG register field. */
#define ALT_NAND_PARAM_FEATURES_GPREG_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_FEATURES_GPREG register field. */
#define ALT_NAND_PARAM_FEATURES_GPREG_MSB        10
/* The width in bits of the ALT_NAND_PARAM_FEATURES_GPREG register field. */
#define ALT_NAND_PARAM_FEATURES_GPREG_WIDTH      1
/* The mask used to set the ALT_NAND_PARAM_FEATURES_GPREG register field value. */
#define ALT_NAND_PARAM_FEATURES_GPREG_SET_MSK    0x00000400
/* The mask used to clear the ALT_NAND_PARAM_FEATURES_GPREG register field value. */
#define ALT_NAND_PARAM_FEATURES_GPREG_CLR_MSK    0xfffffbff
/* The reset value of the ALT_NAND_PARAM_FEATURES_GPREG register field. */
#define ALT_NAND_PARAM_FEATURES_GPREG_RESET      0x0
/* Extracts the ALT_NAND_PARAM_FEATURES_GPREG field value from a register. */
#define ALT_NAND_PARAM_FEATURES_GPREG_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_NAND_PARAM_FEATURES_GPREG register field value suitable for setting the register. */
#define ALT_NAND_PARAM_FEATURES_GPREG_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : index_addr
 * 
 * if set, hardware support only Indexed addressing.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_FEATURES_INDEX_ADDR register field. */
#define ALT_NAND_PARAM_FEATURES_INDEX_ADDR_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_FEATURES_INDEX_ADDR register field. */
#define ALT_NAND_PARAM_FEATURES_INDEX_ADDR_MSB        11
/* The width in bits of the ALT_NAND_PARAM_FEATURES_INDEX_ADDR register field. */
#define ALT_NAND_PARAM_FEATURES_INDEX_ADDR_WIDTH      1
/* The mask used to set the ALT_NAND_PARAM_FEATURES_INDEX_ADDR register field value. */
#define ALT_NAND_PARAM_FEATURES_INDEX_ADDR_SET_MSK    0x00000800
/* The mask used to clear the ALT_NAND_PARAM_FEATURES_INDEX_ADDR register field value. */
#define ALT_NAND_PARAM_FEATURES_INDEX_ADDR_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_NAND_PARAM_FEATURES_INDEX_ADDR register field. */
#define ALT_NAND_PARAM_FEATURES_INDEX_ADDR_RESET      0x1
/* Extracts the ALT_NAND_PARAM_FEATURES_INDEX_ADDR field value from a register. */
#define ALT_NAND_PARAM_FEATURES_INDEX_ADDR_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_NAND_PARAM_FEATURES_INDEX_ADDR register field value suitable for setting the register. */
#define ALT_NAND_PARAM_FEATURES_INDEX_ADDR_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : dfi_intf
 * 
 * if set, hardware supports ONFI2.x synchronous interface.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_FEATURES_DFI_INTF register field. */
#define ALT_NAND_PARAM_FEATURES_DFI_INTF_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_FEATURES_DFI_INTF register field. */
#define ALT_NAND_PARAM_FEATURES_DFI_INTF_MSB        12
/* The width in bits of the ALT_NAND_PARAM_FEATURES_DFI_INTF register field. */
#define ALT_NAND_PARAM_FEATURES_DFI_INTF_WIDTH      1
/* The mask used to set the ALT_NAND_PARAM_FEATURES_DFI_INTF register field value. */
#define ALT_NAND_PARAM_FEATURES_DFI_INTF_SET_MSK    0x00001000
/* The mask used to clear the ALT_NAND_PARAM_FEATURES_DFI_INTF register field value. */
#define ALT_NAND_PARAM_FEATURES_DFI_INTF_CLR_MSK    0xffffefff
/* The reset value of the ALT_NAND_PARAM_FEATURES_DFI_INTF register field. */
#define ALT_NAND_PARAM_FEATURES_DFI_INTF_RESET      0x0
/* Extracts the ALT_NAND_PARAM_FEATURES_DFI_INTF field value from a register. */
#define ALT_NAND_PARAM_FEATURES_DFI_INTF_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_NAND_PARAM_FEATURES_DFI_INTF register field value suitable for setting the register. */
#define ALT_NAND_PARAM_FEATURES_DFI_INTF_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : lba
 * 
 * if set, hardware supports Toshiba LBA devices.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_PARAM_FEATURES_LBA register field. */
#define ALT_NAND_PARAM_FEATURES_LBA_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_NAND_PARAM_FEATURES_LBA register field. */
#define ALT_NAND_PARAM_FEATURES_LBA_MSB        13
/* The width in bits of the ALT_NAND_PARAM_FEATURES_LBA register field. */
#define ALT_NAND_PARAM_FEATURES_LBA_WIDTH      1
/* The mask used to set the ALT_NAND_PARAM_FEATURES_LBA register field value. */
#define ALT_NAND_PARAM_FEATURES_LBA_SET_MSK    0x00002000
/* The mask used to clear the ALT_NAND_PARAM_FEATURES_LBA register field value. */
#define ALT_NAND_PARAM_FEATURES_LBA_CLR_MSK    0xffffdfff
/* The reset value of the ALT_NAND_PARAM_FEATURES_LBA register field. */
#define ALT_NAND_PARAM_FEATURES_LBA_RESET      0x0
/* Extracts the ALT_NAND_PARAM_FEATURES_LBA field value from a register. */
#define ALT_NAND_PARAM_FEATURES_LBA_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_NAND_PARAM_FEATURES_LBA register field value suitable for setting the register. */
#define ALT_NAND_PARAM_FEATURES_LBA_SET(value) (((value) << 13) & 0x00002000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_PARAM_FEATURES.
 */
struct ALT_NAND_PARAM_FEATURES_s
{
    const uint32_t  n_banks       :  2;  /* ALT_NAND_PARAM_FEATURES_N_BANKS */
    uint32_t                      :  4;  /* *UNDEFINED* */
    const uint32_t  dma           :  1;  /* ALT_NAND_PARAM_FEATURES_DMA */
    const uint32_t  cmd_dma       :  1;  /* ALT_NAND_PARAM_FEATURES_CMD_DMA */
    const uint32_t  partition     :  1;  /* ALT_NAND_PARAM_FEATURES_PARTITION */
    const uint32_t  xdma_sideband :  1;  /* ALT_NAND_PARAM_FEATURES_XDMA_SIDEBAND */
    const uint32_t  gpreg         :  1;  /* ALT_NAND_PARAM_FEATURES_GPREG */
    const uint32_t  index_addr    :  1;  /* ALT_NAND_PARAM_FEATURES_INDEX_ADDR */
    const uint32_t  dfi_intf      :  1;  /* ALT_NAND_PARAM_FEATURES_DFI_INTF */
    const uint32_t  lba           :  1;  /* ALT_NAND_PARAM_FEATURES_LBA */
    uint32_t                      : 18;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_PARAM_FEATURES. */
typedef volatile struct ALT_NAND_PARAM_FEATURES_s  ALT_NAND_PARAM_FEATURES_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_PARAM_FEATURES register from the beginning of the component. */
#define ALT_NAND_PARAM_FEATURES_OFST        0xf0

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_NAND_PARAM.
 */
struct ALT_NAND_PARAM_s
{
    volatile ALT_NAND_PARAM_MANUFACTURER_ID_t            manufacturer_id;                     /* ALT_NAND_PARAM_MANUFACTURER_ID */
    volatile uint32_t                                    _pad_0x4_0xf[3];                     /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_DEVICE_ID_t                  device_id;                           /* ALT_NAND_PARAM_DEVICE_ID */
    volatile uint32_t                                    _pad_0x14_0x1f[3];                   /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_DEVICE_PARAM_0_t             device_param_0;                      /* ALT_NAND_PARAM_DEVICE_PARAM_0 */
    volatile uint32_t                                    _pad_0x24_0x2f[3];                   /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_DEVICE_PARAM_1_t             device_param_1;                      /* ALT_NAND_PARAM_DEVICE_PARAM_1 */
    volatile uint32_t                                    _pad_0x34_0x3f[3];                   /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_DEVICE_PARAM_2_t             device_param_2;                      /* ALT_NAND_PARAM_DEVICE_PARAM_2 */
    volatile uint32_t                                    _pad_0x44_0x4f[3];                   /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE_t     logical_page_data_size;              /* ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE */
    volatile uint32_t                                    _pad_0x54_0x5f[3];                   /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE_t    logical_page_spare_size;             /* ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE */
    volatile uint32_t                                    _pad_0x64_0x6f[3];                   /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_REVISION_t                   revision;                            /* ALT_NAND_PARAM_REVISION */
    volatile uint32_t                                    _pad_0x74_0x7f[3];                   /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_ONFI_DEV_FEATURES_t          onfi_device_features;                /* ALT_NAND_PARAM_ONFI_DEV_FEATURES */
    volatile uint32_t                                    _pad_0x84_0x8f[3];                   /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS_t         onfi_optional_commands;              /* ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS */
    volatile uint32_t                                    _pad_0x94_0x9f[3];                   /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_ONFI_TIMING_MOD_t            onfi_timing_mode;                    /* ALT_NAND_PARAM_ONFI_TIMING_MOD */
    volatile uint32_t                                    _pad_0xa4_0xaf[3];                   /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD_t  onfi_pgm_cache_timing_mode;          /* ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD */
    volatile uint32_t                                    _pad_0xb4_0xbf[3];                   /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS_t        onfi_device_no_of_luns;              /* ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS */
    volatile uint32_t                                    _pad_0xc4_0xcf[3];                   /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L_t    onfi_device_no_of_blocks_per_lun_l;  /* ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L */
    volatile uint32_t                                    _pad_0xd4_0xdf[3];                   /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U_t    onfi_device_no_of_blocks_per_lun_u;  /* ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U */
    volatile uint32_t                                    _pad_0xe4_0xef[3];                   /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_FEATURES_t                   features;                            /* ALT_NAND_PARAM_FEATURES */
};

/* The typedef declaration for register group ALT_NAND_PARAM. */
typedef volatile struct ALT_NAND_PARAM_s  ALT_NAND_PARAM_t;
/* The struct declaration for the raw register contents of register group ALT_NAND_PARAM. */
struct ALT_NAND_PARAM_raw_s
{
    volatile uint32_t  manufacturer_id;                     /* ALT_NAND_PARAM_MANUFACTURER_ID */
    volatile uint32_t  _pad_0x4_0xf[3];                     /* *UNDEFINED* */
    volatile uint32_t  device_id;                           /* ALT_NAND_PARAM_DEVICE_ID */
    volatile uint32_t  _pad_0x14_0x1f[3];                   /* *UNDEFINED* */
    volatile uint32_t  device_param_0;                      /* ALT_NAND_PARAM_DEVICE_PARAM_0 */
    volatile uint32_t  _pad_0x24_0x2f[3];                   /* *UNDEFINED* */
    volatile uint32_t  device_param_1;                      /* ALT_NAND_PARAM_DEVICE_PARAM_1 */
    volatile uint32_t  _pad_0x34_0x3f[3];                   /* *UNDEFINED* */
    volatile uint32_t  device_param_2;                      /* ALT_NAND_PARAM_DEVICE_PARAM_2 */
    volatile uint32_t  _pad_0x44_0x4f[3];                   /* *UNDEFINED* */
    volatile uint32_t  logical_page_data_size;              /* ALT_NAND_PARAM_LOGICAL_PAGE_DATA_SIZE */
    volatile uint32_t  _pad_0x54_0x5f[3];                   /* *UNDEFINED* */
    volatile uint32_t  logical_page_spare_size;             /* ALT_NAND_PARAM_LOGICAL_PAGE_SPARE_SIZE */
    volatile uint32_t  _pad_0x64_0x6f[3];                   /* *UNDEFINED* */
    volatile uint32_t  revision;                            /* ALT_NAND_PARAM_REVISION */
    volatile uint32_t  _pad_0x74_0x7f[3];                   /* *UNDEFINED* */
    volatile uint32_t  onfi_device_features;                /* ALT_NAND_PARAM_ONFI_DEV_FEATURES */
    volatile uint32_t  _pad_0x84_0x8f[3];                   /* *UNDEFINED* */
    volatile uint32_t  onfi_optional_commands;              /* ALT_NAND_PARAM_ONFI_OPTIONAL_CMDS */
    volatile uint32_t  _pad_0x94_0x9f[3];                   /* *UNDEFINED* */
    volatile uint32_t  onfi_timing_mode;                    /* ALT_NAND_PARAM_ONFI_TIMING_MOD */
    volatile uint32_t  _pad_0xa4_0xaf[3];                   /* *UNDEFINED* */
    volatile uint32_t  onfi_pgm_cache_timing_mode;          /* ALT_NAND_PARAM_ONFI_PGM_CACHE_TIMING_MOD */
    volatile uint32_t  _pad_0xb4_0xbf[3];                   /* *UNDEFINED* */
    volatile uint32_t  onfi_device_no_of_luns;              /* ALT_NAND_PARAM_ONFI_DEV_NO_OF_LUNS */
    volatile uint32_t  _pad_0xc4_0xcf[3];                   /* *UNDEFINED* */
    volatile uint32_t  onfi_device_no_of_blocks_per_lun_l;  /* ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_L */
    volatile uint32_t  _pad_0xd4_0xdf[3];                   /* *UNDEFINED* */
    volatile uint32_t  onfi_device_no_of_blocks_per_lun_u;  /* ALT_NAND_PARAM_ONFI_DEV_BLKS_PER_LUN_U */
    volatile uint32_t  _pad_0xe4_0xef[3];                   /* *UNDEFINED* */
    volatile uint32_t  features;                            /* ALT_NAND_PARAM_FEATURES */
};

/* The typedef declaration for the raw register contents of register group ALT_NAND_PARAM. */
typedef volatile struct ALT_NAND_PARAM_raw_s  ALT_NAND_PARAM_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : Interrupt and Status Registers - ALT_NAND_STAT
 * Interrupt and Status Registers
 * 
 * Contains interrupt and status registers of controller accessible by software.
 * 
 */
/*
 * Register : transfer_mode
 * 
 * Current data transfer mode is Main only, Spare only or Main+Spare. This
 * information is per bank.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                 
 * :-------|:-------|:------|:-----------------------------
 *  [1:0]  | R      | 0x0   | ALT_NAND_STAT_TFR_MOD_VALUE0
 *  [3:2]  | R      | 0x0   | ALT_NAND_STAT_TFR_MOD_VALUE1
 *  [5:4]  | R      | 0x0   | ALT_NAND_STAT_TFR_MOD_VALUE2
 *  [7:6]  | R      | 0x0   | ALT_NAND_STAT_TFR_MOD_VALUE3
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                 
 * 
 */
/*
 * Field : value0
 * 
 * [list][*]00 - Bank 0 is in Main mode [*]01 - Bank 0 is in Spare mode [*]10 -
 * Bank 0 is in Main+Spare mode[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_TFR_MOD_VALUE0 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_TFR_MOD_VALUE0 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE0_MSB        1
/* The width in bits of the ALT_NAND_STAT_TFR_MOD_VALUE0 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE0_WIDTH      2
/* The mask used to set the ALT_NAND_STAT_TFR_MOD_VALUE0 register field value. */
#define ALT_NAND_STAT_TFR_MOD_VALUE0_SET_MSK    0x00000003
/* The mask used to clear the ALT_NAND_STAT_TFR_MOD_VALUE0 register field value. */
#define ALT_NAND_STAT_TFR_MOD_VALUE0_CLR_MSK    0xfffffffc
/* The reset value of the ALT_NAND_STAT_TFR_MOD_VALUE0 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE0_RESET      0x0
/* Extracts the ALT_NAND_STAT_TFR_MOD_VALUE0 field value from a register. */
#define ALT_NAND_STAT_TFR_MOD_VALUE0_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_NAND_STAT_TFR_MOD_VALUE0 register field value suitable for setting the register. */
#define ALT_NAND_STAT_TFR_MOD_VALUE0_SET(value) (((value) << 0) & 0x00000003)

/*
 * Field : value1
 * 
 * [list][*]00 - Bank 1 is in Main mode [*]01 - Bank 1 is in Spare mode [*]10 -
 * Bank 1 is in Main+Spare mode[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_TFR_MOD_VALUE1 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE1_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_TFR_MOD_VALUE1 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE1_MSB        3
/* The width in bits of the ALT_NAND_STAT_TFR_MOD_VALUE1 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE1_WIDTH      2
/* The mask used to set the ALT_NAND_STAT_TFR_MOD_VALUE1 register field value. */
#define ALT_NAND_STAT_TFR_MOD_VALUE1_SET_MSK    0x0000000c
/* The mask used to clear the ALT_NAND_STAT_TFR_MOD_VALUE1 register field value. */
#define ALT_NAND_STAT_TFR_MOD_VALUE1_CLR_MSK    0xfffffff3
/* The reset value of the ALT_NAND_STAT_TFR_MOD_VALUE1 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE1_RESET      0x0
/* Extracts the ALT_NAND_STAT_TFR_MOD_VALUE1 field value from a register. */
#define ALT_NAND_STAT_TFR_MOD_VALUE1_GET(value) (((value) & 0x0000000c) >> 2)
/* Produces a ALT_NAND_STAT_TFR_MOD_VALUE1 register field value suitable for setting the register. */
#define ALT_NAND_STAT_TFR_MOD_VALUE1_SET(value) (((value) << 2) & 0x0000000c)

/*
 * Field : value2
 * 
 * [list][*]00 - Bank 2 is in Main mode [*]01 - Bank 2 is in Spare mode [*]10 -
 * Bank 2 is in Main+Spare mode[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_TFR_MOD_VALUE2 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE2_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_TFR_MOD_VALUE2 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE2_MSB        5
/* The width in bits of the ALT_NAND_STAT_TFR_MOD_VALUE2 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE2_WIDTH      2
/* The mask used to set the ALT_NAND_STAT_TFR_MOD_VALUE2 register field value. */
#define ALT_NAND_STAT_TFR_MOD_VALUE2_SET_MSK    0x00000030
/* The mask used to clear the ALT_NAND_STAT_TFR_MOD_VALUE2 register field value. */
#define ALT_NAND_STAT_TFR_MOD_VALUE2_CLR_MSK    0xffffffcf
/* The reset value of the ALT_NAND_STAT_TFR_MOD_VALUE2 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE2_RESET      0x0
/* Extracts the ALT_NAND_STAT_TFR_MOD_VALUE2 field value from a register. */
#define ALT_NAND_STAT_TFR_MOD_VALUE2_GET(value) (((value) & 0x00000030) >> 4)
/* Produces a ALT_NAND_STAT_TFR_MOD_VALUE2 register field value suitable for setting the register. */
#define ALT_NAND_STAT_TFR_MOD_VALUE2_SET(value) (((value) << 4) & 0x00000030)

/*
 * Field : value3
 * 
 * [list][*]00 - Bank 3 is in Main mode [*]01 - Bank 3 is in Spare mode [*]10 -
 * Bank 3 is in Main+Spare mode[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_TFR_MOD_VALUE3 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE3_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_TFR_MOD_VALUE3 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE3_MSB        7
/* The width in bits of the ALT_NAND_STAT_TFR_MOD_VALUE3 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE3_WIDTH      2
/* The mask used to set the ALT_NAND_STAT_TFR_MOD_VALUE3 register field value. */
#define ALT_NAND_STAT_TFR_MOD_VALUE3_SET_MSK    0x000000c0
/* The mask used to clear the ALT_NAND_STAT_TFR_MOD_VALUE3 register field value. */
#define ALT_NAND_STAT_TFR_MOD_VALUE3_CLR_MSK    0xffffff3f
/* The reset value of the ALT_NAND_STAT_TFR_MOD_VALUE3 register field. */
#define ALT_NAND_STAT_TFR_MOD_VALUE3_RESET      0x0
/* Extracts the ALT_NAND_STAT_TFR_MOD_VALUE3 field value from a register. */
#define ALT_NAND_STAT_TFR_MOD_VALUE3_GET(value) (((value) & 0x000000c0) >> 6)
/* Produces a ALT_NAND_STAT_TFR_MOD_VALUE3 register field value suitable for setting the register. */
#define ALT_NAND_STAT_TFR_MOD_VALUE3_SET(value) (((value) << 6) & 0x000000c0)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_TFR_MOD.
 */
struct ALT_NAND_STAT_TFR_MOD_s
{
    const uint32_t  value0 :  2;  /* ALT_NAND_STAT_TFR_MOD_VALUE0 */
    const uint32_t  value1 :  2;  /* ALT_NAND_STAT_TFR_MOD_VALUE1 */
    const uint32_t  value2 :  2;  /* ALT_NAND_STAT_TFR_MOD_VALUE2 */
    const uint32_t  value3 :  2;  /* ALT_NAND_STAT_TFR_MOD_VALUE3 */
    uint32_t               : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_TFR_MOD. */
typedef volatile struct ALT_NAND_STAT_TFR_MOD_s  ALT_NAND_STAT_TFR_MOD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_TFR_MOD register from the beginning of the component. */
#define ALT_NAND_STAT_TFR_MOD_OFST        0x0

/*
 * Register : intr_status0
 * 
 * Interrupt status register for bank 0
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                  
 * :--------|:-------|:------|:----------------------------------------------
 *  [0]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR       
 *  [1]     | ???    | 0x0   | *UNDEFINED*                                  
 *  [2]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP        
 *  [3]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_TIME_OUT            
 *  [4]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL        
 *  [5]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL          
 *  [6]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_LD_COMP             
 *  [7]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP        
 *  [8]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_ERASE_COMP          
 *  [9]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP
 *  [10]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK          
 *  [11]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD           
 *  [12]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_INT_ACT             
 *  [13]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_RST_COMP            
 *  [14]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR        
 *  [15]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC       
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                                  
 * 
 */
/*
 * Field : ecc_uncor_err
 * 
 * Ecc logic detected uncorrectable error while reading data from flash device.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR_MSB        0
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : dma_cmd_comp
 * 
 * Not implemented.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP_MSB        2
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP_SET_MSK    0x00000004
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP_CLR_MSK    0xfffffffb
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : time_out
 * 
 * Watchdog timer has triggered in the controller due to one of the reasons like
 * device not responding or controller state machine did not get back to idle
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT0_TIME_OUT_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT0_TIME_OUT_MSB        3
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT0_TIME_OUT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_STAT0_TIME_OUT_SET_MSK    0x00000008
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_STAT0_TIME_OUT_CLR_MSK    0xfffffff7
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT0_TIME_OUT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_TIME_OUT field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_TIME_OUT_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_NAND_STAT_INTR_STAT0_TIME_OUT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_TIME_OUT_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : program_fail
 * 
 * Program failure occurred in the device on issuance of a program command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed program operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL_MSB        4
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL_SET_MSK    0x00000010
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL_CLR_MSK    0xffffffef
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : erase_fail
 * 
 * Erase failure occurred in the device on issuance of a erase command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed erase operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL_MSB        5
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL_SET_MSK    0x00000020
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL_CLR_MSK    0xffffffdf
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : load_comp
 * 
 * Device finished the last issued load command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_LD_COMP_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_LD_COMP_MSB        6
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_LD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT0_LD_COMP_SET_MSK    0x00000040
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT0_LD_COMP_CLR_MSK    0xffffffbf
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_LD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_LD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_LD_COMP_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_NAND_STAT_INTR_STAT0_LD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_LD_COMP_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : program_comp
 * 
 * Device finished the last issued program command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP_MSB        7
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP_SET_MSK    0x00000080
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP_CLR_MSK    0xffffff7f
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : erase_comp
 * 
 * Device erase operation complete
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_COMP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_COMP_MSB        8
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_COMP_SET_MSK    0x00000100
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_COMP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_ERASE_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_COMP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_NAND_STAT_INTR_STAT0_ERASE_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_ERASE_COMP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : pipe_cpybck_cmd_comp
 * 
 * A pipeline command or a copyback bank command has completed on this particular
 * bank
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP_MSB        9
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP_SET_MSK    0x00000200
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : locked_blk
 * 
 * The address to program or erase operation is to a locked block and the operation
 * failed due to this reason
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK_MSB        10
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK_SET_MSK    0x00000400
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK_CLR_MSK    0xfffffbff
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : unsup_cmd
 * 
 * An unsupported command was received. This interrupt is set when an invalid
 * command is received, or when a command sequence is broken.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD_MSB        11
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD_SET_MSK    0x00000800
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : INT_act
 * 
 * R/B pin of device transitioned from low to high
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT0_INT_ACT_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT0_INT_ACT_MSB        12
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT0_INT_ACT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_STAT0_INT_ACT_SET_MSK    0x00001000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_STAT0_INT_ACT_CLR_MSK    0xffffefff
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT0_INT_ACT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_INT_ACT field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_INT_ACT_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_NAND_STAT_INTR_STAT0_INT_ACT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_INT_ACT_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : rst_comp
 * 
 * Controller has finished reset and initialization process
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_RST_COMP_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_RST_COMP_MSB        13
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_RST_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT0_RST_COMP_SET_MSK    0x00002000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT0_RST_COMP_CLR_MSK    0xffffdfff
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT0_RST_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_RST_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_RST_COMP_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_NAND_STAT_INTR_STAT0_RST_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_RST_COMP_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : pipe_cmd_err
 * 
 * A pipeline command sequence has been violated. This occurs when Map 01 page
 * read/write address does not match the corresponding expected address from the
 * pipeline commands issued earlier.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR_MSB        14
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR_SET_MSK    0x00004000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR_CLR_MSK    0xffffbfff
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : page_xfer_inc
 * 
 * For every page of data transfer to or from the device, this bit will be set.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC_MSB        15
/* The width in bits of the ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC_SET_MSK    0x00008000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC_CLR_MSK    0xffff7fff
/* The reset value of the ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC field value from a register. */
#define ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC_SET(value) (((value) << 15) & 0x00008000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_INTR_STAT0.
 */
struct ALT_NAND_STAT_INTR_STAT0_s
{
    uint32_t  ecc_uncor_err        :  1;  /* ALT_NAND_STAT_INTR_STAT0_ECC_UNCOR_ERR */
    uint32_t                       :  1;  /* *UNDEFINED* */
    uint32_t  dma_cmd_comp         :  1;  /* ALT_NAND_STAT_INTR_STAT0_DMA_CMD_COMP */
    uint32_t  time_out             :  1;  /* ALT_NAND_STAT_INTR_STAT0_TIME_OUT */
    uint32_t  program_fail         :  1;  /* ALT_NAND_STAT_INTR_STAT0_PROGRAM_FAIL */
    uint32_t  erase_fail           :  1;  /* ALT_NAND_STAT_INTR_STAT0_ERASE_FAIL */
    uint32_t  load_comp            :  1;  /* ALT_NAND_STAT_INTR_STAT0_LD_COMP */
    uint32_t  program_comp         :  1;  /* ALT_NAND_STAT_INTR_STAT0_PROGRAM_COMP */
    uint32_t  erase_comp           :  1;  /* ALT_NAND_STAT_INTR_STAT0_ERASE_COMP */
    uint32_t  pipe_cpybck_cmd_comp :  1;  /* ALT_NAND_STAT_INTR_STAT0_PIPE_CPYBCK_CMD_COMP */
    uint32_t  locked_blk           :  1;  /* ALT_NAND_STAT_INTR_STAT0_LOCKED_BLK */
    uint32_t  unsup_cmd            :  1;  /* ALT_NAND_STAT_INTR_STAT0_UNSUP_CMD */
    uint32_t  INT_act              :  1;  /* ALT_NAND_STAT_INTR_STAT0_INT_ACT */
    uint32_t  rst_comp             :  1;  /* ALT_NAND_STAT_INTR_STAT0_RST_COMP */
    uint32_t  pipe_cmd_err         :  1;  /* ALT_NAND_STAT_INTR_STAT0_PIPE_CMD_ERR */
    uint32_t  page_xfer_inc        :  1;  /* ALT_NAND_STAT_INTR_STAT0_PAGE_XFER_INC */
    uint32_t                       : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_INTR_STAT0. */
typedef volatile struct ALT_NAND_STAT_INTR_STAT0_s  ALT_NAND_STAT_INTR_STAT0_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_INTR_STAT0 register from the beginning of the component. */
#define ALT_NAND_STAT_INTR_STAT0_OFST        0x10

/*
 * Register : intr_en0
 * 
 * Enables corresponding interrupt bit in interrupt register for bank 0
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                
 * :--------|:-------|:------|:--------------------------------------------
 *  [0]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR       
 *  [1]     | ???    | 0x0   | *UNDEFINED*                                
 *  [2]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP        
 *  [3]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN0_TIME_OUT            
 *  [4]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL        
 *  [5]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN0_ERASE_FAIL          
 *  [6]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN0_LD_COMP             
 *  [7]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP        
 *  [8]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN0_ERASE_COMP          
 *  [9]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP
 *  [10]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN0_LOCKED_BLK          
 *  [11]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN0_UNSUP_CMD           
 *  [12]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN0_INT_ACT             
 *  [13]    | RW     | 0x1   | ALT_NAND_STAT_INTR_EN0_RST_COMP            
 *  [14]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR        
 *  [15]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC       
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                                
 * 
 */
/*
 * Field : ecc_uncor_err
 * 
 * If set, Controller will interrupt processor when Ecc logic detects uncorrectable
 * error.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR_MSB        0
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : dma_cmd_comp
 * 
 * Not implemented.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP_MSB        2
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP_SET_MSK    0x00000004
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP_CLR_MSK    0xfffffffb
/* The reset value of the ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : time_out
 * 
 * Watchdog timer has triggered in the controller due to one of the reasons like
 * device not responding or controller state machine did not get back to idle
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN0_TIME_OUT_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN0_TIME_OUT_MSB        3
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN0_TIME_OUT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_EN0_TIME_OUT_SET_MSK    0x00000008
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_EN0_TIME_OUT_CLR_MSK    0xfffffff7
/* The reset value of the ALT_NAND_STAT_INTR_EN0_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN0_TIME_OUT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN0_TIME_OUT field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_TIME_OUT_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_NAND_STAT_INTR_EN0_TIME_OUT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_TIME_OUT_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : program_fail
 * 
 * Program failure occurred in the device on issuance of a program command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed program operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL_MSB        4
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL_SET_MSK    0x00000010
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL_CLR_MSK    0xffffffef
/* The reset value of the ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : erase_fail
 * 
 * Erase failure occurred in the device on issuance of a erase command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed erase operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_FAIL_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_FAIL_MSB        5
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_FAIL_SET_MSK    0x00000020
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_FAIL_CLR_MSK    0xffffffdf
/* The reset value of the ALT_NAND_STAT_INTR_EN0_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN0_ERASE_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_FAIL_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_NAND_STAT_INTR_EN0_ERASE_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_FAIL_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : load_comp
 * 
 * Device finished the last issued load command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_LD_COMP_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_LD_COMP_MSB        6
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_LD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN0_LD_COMP_SET_MSK    0x00000040
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN0_LD_COMP_CLR_MSK    0xffffffbf
/* The reset value of the ALT_NAND_STAT_INTR_EN0_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_LD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN0_LD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_LD_COMP_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_NAND_STAT_INTR_EN0_LD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_LD_COMP_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : program_comp
 * 
 * Device finished the last issued program command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP_MSB        7
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP_SET_MSK    0x00000080
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP_CLR_MSK    0xffffff7f
/* The reset value of the ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : erase_comp
 * 
 * Device erase operation complete
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_COMP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_COMP_MSB        8
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_COMP_SET_MSK    0x00000100
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_COMP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_NAND_STAT_INTR_EN0_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN0_ERASE_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_COMP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_NAND_STAT_INTR_EN0_ERASE_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_ERASE_COMP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : pipe_cpybck_cmd_comp
 * 
 * A pipeline command or a copyback bank command has completed on this particular
 * bank
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP_MSB        9
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP_SET_MSK    0x00000200
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : locked_blk
 * 
 * The address to program or erase operation is to a locked block and the operation
 * failed due to this reason
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN0_LOCKED_BLK_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN0_LOCKED_BLK_MSB        10
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN0_LOCKED_BLK_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_EN0_LOCKED_BLK_SET_MSK    0x00000400
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_EN0_LOCKED_BLK_CLR_MSK    0xfffffbff
/* The reset value of the ALT_NAND_STAT_INTR_EN0_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN0_LOCKED_BLK_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN0_LOCKED_BLK field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_LOCKED_BLK_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_NAND_STAT_INTR_EN0_LOCKED_BLK register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_LOCKED_BLK_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : unsup_cmd
 * 
 * An unsupported command was received. This interrupt is set when an invalid
 * command is received, or when a command sequence is broken.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN0_UNSUP_CMD_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN0_UNSUP_CMD_MSB        11
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN0_UNSUP_CMD_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_EN0_UNSUP_CMD_SET_MSK    0x00000800
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_EN0_UNSUP_CMD_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_NAND_STAT_INTR_EN0_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN0_UNSUP_CMD_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN0_UNSUP_CMD field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_UNSUP_CMD_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_NAND_STAT_INTR_EN0_UNSUP_CMD register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_UNSUP_CMD_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : INT_act
 * 
 * R/B pin of device transitioned from low to high
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN0_INT_ACT_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN0_INT_ACT_MSB        12
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN0_INT_ACT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_EN0_INT_ACT_SET_MSK    0x00001000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_EN0_INT_ACT_CLR_MSK    0xffffefff
/* The reset value of the ALT_NAND_STAT_INTR_EN0_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN0_INT_ACT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN0_INT_ACT field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_INT_ACT_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_NAND_STAT_INTR_EN0_INT_ACT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_INT_ACT_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : rst_comp
 * 
 * A reset command has completed on this bank
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_RST_COMP_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_RST_COMP_MSB        13
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_RST_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN0_RST_COMP_SET_MSK    0x00002000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN0_RST_COMP_CLR_MSK    0xffffdfff
/* The reset value of the ALT_NAND_STAT_INTR_EN0_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN0_RST_COMP_RESET      0x1
/* Extracts the ALT_NAND_STAT_INTR_EN0_RST_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_RST_COMP_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_NAND_STAT_INTR_EN0_RST_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_RST_COMP_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : pipe_cmd_err
 * 
 * A pipeline command sequence has been violated. This occurs when Map 01 page
 * read/write address does not match the corresponding expected address from the
 * pipeline commands issued earlier.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR_MSB        14
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR_SET_MSK    0x00004000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR_CLR_MSK    0xffffbfff
/* The reset value of the ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : page_xfer_inc
 * 
 * For every page of data transfer to or from the device, this bit will be set.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC_MSB        15
/* The width in bits of the ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC_SET_MSK    0x00008000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC_CLR_MSK    0xffff7fff
/* The reset value of the ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC field value from a register. */
#define ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC_SET(value) (((value) << 15) & 0x00008000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_INTR_EN0.
 */
struct ALT_NAND_STAT_INTR_EN0_s
{
    uint32_t  ecc_uncor_err        :  1;  /* ALT_NAND_STAT_INTR_EN0_ECC_UNCOR_ERR */
    uint32_t                       :  1;  /* *UNDEFINED* */
    uint32_t  dma_cmd_comp         :  1;  /* ALT_NAND_STAT_INTR_EN0_DMA_CMD_COMP */
    uint32_t  time_out             :  1;  /* ALT_NAND_STAT_INTR_EN0_TIME_OUT */
    uint32_t  program_fail         :  1;  /* ALT_NAND_STAT_INTR_EN0_PROGRAM_FAIL */
    uint32_t  erase_fail           :  1;  /* ALT_NAND_STAT_INTR_EN0_ERASE_FAIL */
    uint32_t  load_comp            :  1;  /* ALT_NAND_STAT_INTR_EN0_LD_COMP */
    uint32_t  program_comp         :  1;  /* ALT_NAND_STAT_INTR_EN0_PROGRAM_COMP */
    uint32_t  erase_comp           :  1;  /* ALT_NAND_STAT_INTR_EN0_ERASE_COMP */
    uint32_t  pipe_cpybck_cmd_comp :  1;  /* ALT_NAND_STAT_INTR_EN0_PIPE_CPYBCK_CMD_COMP */
    uint32_t  locked_blk           :  1;  /* ALT_NAND_STAT_INTR_EN0_LOCKED_BLK */
    uint32_t  unsup_cmd            :  1;  /* ALT_NAND_STAT_INTR_EN0_UNSUP_CMD */
    uint32_t  INT_act              :  1;  /* ALT_NAND_STAT_INTR_EN0_INT_ACT */
    uint32_t  rst_comp             :  1;  /* ALT_NAND_STAT_INTR_EN0_RST_COMP */
    uint32_t  pipe_cmd_err         :  1;  /* ALT_NAND_STAT_INTR_EN0_PIPE_CMD_ERR */
    uint32_t  page_xfer_inc        :  1;  /* ALT_NAND_STAT_INTR_EN0_PAGE_XFER_INC */
    uint32_t                       : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_INTR_EN0. */
typedef volatile struct ALT_NAND_STAT_INTR_EN0_s  ALT_NAND_STAT_INTR_EN0_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_INTR_EN0 register from the beginning of the component. */
#define ALT_NAND_STAT_INTR_EN0_OFST        0x20

/*
 * Register : page_cnt0
 * 
 * Decrementing page count bank 0
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [7:0]  | R      | 0x0   | ALT_NAND_STAT_PAGE_CNT0_VALUE
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : value
 * 
 * Maintains a decrementing count of the number of pages in the multi-page
 * (pipeline and copyback) command being executed.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_PAGE_CNT0_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT0_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_PAGE_CNT0_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT0_VALUE_MSB        7
/* The width in bits of the ALT_NAND_STAT_PAGE_CNT0_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT0_VALUE_WIDTH      8
/* The mask used to set the ALT_NAND_STAT_PAGE_CNT0_VALUE register field value. */
#define ALT_NAND_STAT_PAGE_CNT0_VALUE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_NAND_STAT_PAGE_CNT0_VALUE register field value. */
#define ALT_NAND_STAT_PAGE_CNT0_VALUE_CLR_MSK    0xffffff00
/* The reset value of the ALT_NAND_STAT_PAGE_CNT0_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT0_VALUE_RESET      0x0
/* Extracts the ALT_NAND_STAT_PAGE_CNT0_VALUE field value from a register. */
#define ALT_NAND_STAT_PAGE_CNT0_VALUE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_NAND_STAT_PAGE_CNT0_VALUE register field value suitable for setting the register. */
#define ALT_NAND_STAT_PAGE_CNT0_VALUE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_PAGE_CNT0.
 */
struct ALT_NAND_STAT_PAGE_CNT0_s
{
    const uint32_t  value :  8;  /* ALT_NAND_STAT_PAGE_CNT0_VALUE */
    uint32_t              : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_PAGE_CNT0. */
typedef volatile struct ALT_NAND_STAT_PAGE_CNT0_s  ALT_NAND_STAT_PAGE_CNT0_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_PAGE_CNT0 register from the beginning of the component. */
#define ALT_NAND_STAT_PAGE_CNT0_OFST        0x30

/*
 * Register : err_page_addr0
 * 
 * Erred page address bank 0
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                       
 * :--------|:-------|:------|:-----------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                       
 * 
 */
/*
 * Field : value
 * 
 * Holds the page address that resulted in a failure on program or erase operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE_MSB        15
/* The width in bits of the ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE register field value. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE register field value. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE_RESET      0x0
/* Extracts the ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE field value from a register. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE register field value suitable for setting the register. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_ERR_PAGE_ADDR0.
 */
struct ALT_NAND_STAT_ERR_PAGE_ADDR0_s
{
    const uint32_t  value : 16;  /* ALT_NAND_STAT_ERR_PAGE_ADDR0_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_ERR_PAGE_ADDR0. */
typedef volatile struct ALT_NAND_STAT_ERR_PAGE_ADDR0_s  ALT_NAND_STAT_ERR_PAGE_ADDR0_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_ERR_PAGE_ADDR0 register from the beginning of the component. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR0_OFST        0x40

/*
 * Register : err_block_addr0
 * 
 * Erred block address bank 0
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                        
 * :--------|:-------|:------|:------------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : value
 * 
 * Holds the block address that resulted in a failure on program or erase
 * operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE_MSB        15
/* The width in bits of the ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE register field value. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE register field value. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE_RESET      0x0
/* Extracts the ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE field value from a register. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE register field value suitable for setting the register. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_ERR_BLOCK_ADDR0.
 */
struct ALT_NAND_STAT_ERR_BLOCK_ADDR0_s
{
    const uint32_t  value : 16;  /* ALT_NAND_STAT_ERR_BLOCK_ADDR0_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_ERR_BLOCK_ADDR0. */
typedef volatile struct ALT_NAND_STAT_ERR_BLOCK_ADDR0_s  ALT_NAND_STAT_ERR_BLOCK_ADDR0_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_ERR_BLOCK_ADDR0 register from the beginning of the component. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR0_OFST        0x50

/*
 * Register : intr_status1
 * 
 * Interrupt status register for bank 1
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                  
 * :--------|:-------|:------|:----------------------------------------------
 *  [0]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR       
 *  [1]     | ???    | 0x0   | *UNDEFINED*                                  
 *  [2]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP        
 *  [3]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_TIME_OUT            
 *  [4]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL        
 *  [5]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL          
 *  [6]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_LD_COMP             
 *  [7]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP        
 *  [8]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_ERASE_COMP          
 *  [9]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP
 *  [10]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK          
 *  [11]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD           
 *  [12]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_INT_ACT             
 *  [13]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_RST_COMP            
 *  [14]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR        
 *  [15]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC       
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                                  
 * 
 */
/*
 * Field : ecc_uncor_err
 * 
 * Ecc logic detected uncorrectable error while reading data from flash device.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR_MSB        0
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : dma_cmd_comp
 * 
 * Not implemented.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP_MSB        2
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP_SET_MSK    0x00000004
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP_CLR_MSK    0xfffffffb
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : time_out
 * 
 * Watchdog timer has triggered in the controller due to one of the reasons like
 * device not responding or controller state machine did not get back to idle
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT1_TIME_OUT_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT1_TIME_OUT_MSB        3
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT1_TIME_OUT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_STAT1_TIME_OUT_SET_MSK    0x00000008
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_STAT1_TIME_OUT_CLR_MSK    0xfffffff7
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT1_TIME_OUT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_TIME_OUT field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_TIME_OUT_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_NAND_STAT_INTR_STAT1_TIME_OUT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_TIME_OUT_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : program_fail
 * 
 * Program failure occurred in the device on issuance of a program command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed program operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL_MSB        4
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL_SET_MSK    0x00000010
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL_CLR_MSK    0xffffffef
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : erase_fail
 * 
 * Erase failure occurred in the device on issuance of a erase command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed erase operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL_MSB        5
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL_SET_MSK    0x00000020
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL_CLR_MSK    0xffffffdf
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : load_comp
 * 
 * Device finished the last issued load command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_LD_COMP_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_LD_COMP_MSB        6
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_LD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT1_LD_COMP_SET_MSK    0x00000040
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT1_LD_COMP_CLR_MSK    0xffffffbf
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_LD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_LD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_LD_COMP_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_NAND_STAT_INTR_STAT1_LD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_LD_COMP_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : program_comp
 * 
 * Device finished the last issued program command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP_MSB        7
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP_SET_MSK    0x00000080
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP_CLR_MSK    0xffffff7f
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : erase_comp
 * 
 * Device erase operation complete
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_COMP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_COMP_MSB        8
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_COMP_SET_MSK    0x00000100
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_COMP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_ERASE_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_COMP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_NAND_STAT_INTR_STAT1_ERASE_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_ERASE_COMP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : pipe_cpybck_cmd_comp
 * 
 * A pipeline command or a copyback bank command has completed on this particular
 * bank
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP_MSB        9
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP_SET_MSK    0x00000200
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : locked_blk
 * 
 * The address to program or erase operation is to a locked block and the operation
 * failed due to this reason
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK_MSB        10
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK_SET_MSK    0x00000400
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK_CLR_MSK    0xfffffbff
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : unsup_cmd
 * 
 * An unsupported command was received. This interrupt is set when an invalid
 * command is received, or when a command sequence is broken.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD_MSB        11
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD_SET_MSK    0x00000800
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : INT_act
 * 
 * R/B pin of device transitioned from low to high
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT1_INT_ACT_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT1_INT_ACT_MSB        12
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT1_INT_ACT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_STAT1_INT_ACT_SET_MSK    0x00001000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_STAT1_INT_ACT_CLR_MSK    0xffffefff
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT1_INT_ACT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_INT_ACT field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_INT_ACT_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_NAND_STAT_INTR_STAT1_INT_ACT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_INT_ACT_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : rst_comp
 * 
 * The NAND Flash Memory Controller has completed its reset and initialization
 * process
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_RST_COMP_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_RST_COMP_MSB        13
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_RST_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT1_RST_COMP_SET_MSK    0x00002000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT1_RST_COMP_CLR_MSK    0xffffdfff
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT1_RST_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_RST_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_RST_COMP_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_NAND_STAT_INTR_STAT1_RST_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_RST_COMP_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : pipe_cmd_err
 * 
 * A pipeline command sequence has been violated. This occurs when Map 01 page
 * read/write address does not match the corresponding expected address from the
 * pipeline commands issued earlier.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR_MSB        14
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR_SET_MSK    0x00004000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR_CLR_MSK    0xffffbfff
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : page_xfer_inc
 * 
 * For every page of data transfer to or from the device, this bit will be set.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC_MSB        15
/* The width in bits of the ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC_SET_MSK    0x00008000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC_CLR_MSK    0xffff7fff
/* The reset value of the ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC field value from a register. */
#define ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC_SET(value) (((value) << 15) & 0x00008000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_INTR_STAT1.
 */
struct ALT_NAND_STAT_INTR_STAT1_s
{
    uint32_t  ecc_uncor_err        :  1;  /* ALT_NAND_STAT_INTR_STAT1_ECC_UNCOR_ERR */
    uint32_t                       :  1;  /* *UNDEFINED* */
    uint32_t  dma_cmd_comp         :  1;  /* ALT_NAND_STAT_INTR_STAT1_DMA_CMD_COMP */
    uint32_t  time_out             :  1;  /* ALT_NAND_STAT_INTR_STAT1_TIME_OUT */
    uint32_t  program_fail         :  1;  /* ALT_NAND_STAT_INTR_STAT1_PROGRAM_FAIL */
    uint32_t  erase_fail           :  1;  /* ALT_NAND_STAT_INTR_STAT1_ERASE_FAIL */
    uint32_t  load_comp            :  1;  /* ALT_NAND_STAT_INTR_STAT1_LD_COMP */
    uint32_t  program_comp         :  1;  /* ALT_NAND_STAT_INTR_STAT1_PROGRAM_COMP */
    uint32_t  erase_comp           :  1;  /* ALT_NAND_STAT_INTR_STAT1_ERASE_COMP */
    uint32_t  pipe_cpybck_cmd_comp :  1;  /* ALT_NAND_STAT_INTR_STAT1_PIPE_CPYBCK_CMD_COMP */
    uint32_t  locked_blk           :  1;  /* ALT_NAND_STAT_INTR_STAT1_LOCKED_BLK */
    uint32_t  unsup_cmd            :  1;  /* ALT_NAND_STAT_INTR_STAT1_UNSUP_CMD */
    uint32_t  INT_act              :  1;  /* ALT_NAND_STAT_INTR_STAT1_INT_ACT */
    uint32_t  rst_comp             :  1;  /* ALT_NAND_STAT_INTR_STAT1_RST_COMP */
    uint32_t  pipe_cmd_err         :  1;  /* ALT_NAND_STAT_INTR_STAT1_PIPE_CMD_ERR */
    uint32_t  page_xfer_inc        :  1;  /* ALT_NAND_STAT_INTR_STAT1_PAGE_XFER_INC */
    uint32_t                       : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_INTR_STAT1. */
typedef volatile struct ALT_NAND_STAT_INTR_STAT1_s  ALT_NAND_STAT_INTR_STAT1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_INTR_STAT1 register from the beginning of the component. */
#define ALT_NAND_STAT_INTR_STAT1_OFST        0x60

/*
 * Register : intr_en1
 * 
 * Enables corresponding interrupt bit in interrupt register for bank 1
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                
 * :--------|:-------|:------|:--------------------------------------------
 *  [0]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR       
 *  [1]     | ???    | 0x0   | *UNDEFINED*                                
 *  [2]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP        
 *  [3]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN1_TIME_OUT            
 *  [4]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL        
 *  [5]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN1_ERASE_FAIL          
 *  [6]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN1_LD_COMP             
 *  [7]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP        
 *  [8]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN1_ERASE_COMP          
 *  [9]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP
 *  [10]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN1_LOCKED_BLK          
 *  [11]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN1_UNSUP_CMD           
 *  [12]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN1_INT_ACT             
 *  [13]    | RW     | 0x1   | ALT_NAND_STAT_INTR_EN1_RST_COMP            
 *  [14]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR        
 *  [15]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC       
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                                
 * 
 */
/*
 * Field : ecc_uncor_err
 * 
 * If set, Controller will interrupt processor when Ecc logic detects uncorrectable
 * error.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR_MSB        0
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : dma_cmd_comp
 * 
 * Not implemented.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP_MSB        2
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP_SET_MSK    0x00000004
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP_CLR_MSK    0xfffffffb
/* The reset value of the ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : time_out
 * 
 * Watchdog timer has triggered in the controller due to one of the reasons like
 * device not responding or controller state machine did not get back to idle
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN1_TIME_OUT_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN1_TIME_OUT_MSB        3
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN1_TIME_OUT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_EN1_TIME_OUT_SET_MSK    0x00000008
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_EN1_TIME_OUT_CLR_MSK    0xfffffff7
/* The reset value of the ALT_NAND_STAT_INTR_EN1_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN1_TIME_OUT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN1_TIME_OUT field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_TIME_OUT_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_NAND_STAT_INTR_EN1_TIME_OUT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_TIME_OUT_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : program_fail
 * 
 * Program failure occurred in the device on issuance of a program command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed program operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL_MSB        4
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL_SET_MSK    0x00000010
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL_CLR_MSK    0xffffffef
/* The reset value of the ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : erase_fail
 * 
 * Erase failure occurred in the device on issuance of a erase command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed erase operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_FAIL_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_FAIL_MSB        5
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_FAIL_SET_MSK    0x00000020
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_FAIL_CLR_MSK    0xffffffdf
/* The reset value of the ALT_NAND_STAT_INTR_EN1_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN1_ERASE_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_FAIL_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_NAND_STAT_INTR_EN1_ERASE_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_FAIL_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : load_comp
 * 
 * Device finished the last issued load command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_LD_COMP_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_LD_COMP_MSB        6
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_LD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN1_LD_COMP_SET_MSK    0x00000040
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN1_LD_COMP_CLR_MSK    0xffffffbf
/* The reset value of the ALT_NAND_STAT_INTR_EN1_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_LD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN1_LD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_LD_COMP_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_NAND_STAT_INTR_EN1_LD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_LD_COMP_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : program_comp
 * 
 * Device finished the last issued program command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP_MSB        7
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP_SET_MSK    0x00000080
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP_CLR_MSK    0xffffff7f
/* The reset value of the ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : erase_comp
 * 
 * Device erase operation complete
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_COMP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_COMP_MSB        8
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_COMP_SET_MSK    0x00000100
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_COMP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_NAND_STAT_INTR_EN1_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN1_ERASE_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_COMP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_NAND_STAT_INTR_EN1_ERASE_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_ERASE_COMP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : pipe_cpybck_cmd_comp
 * 
 * A pipeline command or a copyback bank command has completed on this particular
 * bank
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP_MSB        9
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP_SET_MSK    0x00000200
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : locked_blk
 * 
 * The address to program or erase operation is to a locked block and the operation
 * failed due to this reason
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN1_LOCKED_BLK_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN1_LOCKED_BLK_MSB        10
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN1_LOCKED_BLK_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_EN1_LOCKED_BLK_SET_MSK    0x00000400
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_EN1_LOCKED_BLK_CLR_MSK    0xfffffbff
/* The reset value of the ALT_NAND_STAT_INTR_EN1_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN1_LOCKED_BLK_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN1_LOCKED_BLK field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_LOCKED_BLK_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_NAND_STAT_INTR_EN1_LOCKED_BLK register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_LOCKED_BLK_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : unsup_cmd
 * 
 * An unsupported command was received. This interrupt is set when an invalid
 * command is received, or when a command sequence is broken.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN1_UNSUP_CMD_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN1_UNSUP_CMD_MSB        11
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN1_UNSUP_CMD_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_EN1_UNSUP_CMD_SET_MSK    0x00000800
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_EN1_UNSUP_CMD_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_NAND_STAT_INTR_EN1_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN1_UNSUP_CMD_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN1_UNSUP_CMD field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_UNSUP_CMD_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_NAND_STAT_INTR_EN1_UNSUP_CMD register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_UNSUP_CMD_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : INT_act
 * 
 * R/B pin of device transitioned from low to high
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN1_INT_ACT_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN1_INT_ACT_MSB        12
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN1_INT_ACT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_EN1_INT_ACT_SET_MSK    0x00001000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_EN1_INT_ACT_CLR_MSK    0xffffefff
/* The reset value of the ALT_NAND_STAT_INTR_EN1_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN1_INT_ACT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN1_INT_ACT field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_INT_ACT_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_NAND_STAT_INTR_EN1_INT_ACT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_INT_ACT_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : rst_comp
 * 
 * A reset command has completed on this bank
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_RST_COMP_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_RST_COMP_MSB        13
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_RST_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN1_RST_COMP_SET_MSK    0x00002000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN1_RST_COMP_CLR_MSK    0xffffdfff
/* The reset value of the ALT_NAND_STAT_INTR_EN1_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN1_RST_COMP_RESET      0x1
/* Extracts the ALT_NAND_STAT_INTR_EN1_RST_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_RST_COMP_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_NAND_STAT_INTR_EN1_RST_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_RST_COMP_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : pipe_cmd_err
 * 
 * A pipeline command sequence has been violated. This occurs when Map 01 page
 * read/write address does not match the corresponding expected address from the
 * pipeline commands issued earlier.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR_MSB        14
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR_SET_MSK    0x00004000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR_CLR_MSK    0xffffbfff
/* The reset value of the ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : page_xfer_inc
 * 
 * For every page of data transfer to or from the device, this bit will be set.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC_MSB        15
/* The width in bits of the ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC_SET_MSK    0x00008000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC_CLR_MSK    0xffff7fff
/* The reset value of the ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC field value from a register. */
#define ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC_SET(value) (((value) << 15) & 0x00008000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_INTR_EN1.
 */
struct ALT_NAND_STAT_INTR_EN1_s
{
    uint32_t  ecc_uncor_err        :  1;  /* ALT_NAND_STAT_INTR_EN1_ECC_UNCOR_ERR */
    uint32_t                       :  1;  /* *UNDEFINED* */
    uint32_t  dma_cmd_comp         :  1;  /* ALT_NAND_STAT_INTR_EN1_DMA_CMD_COMP */
    uint32_t  time_out             :  1;  /* ALT_NAND_STAT_INTR_EN1_TIME_OUT */
    uint32_t  program_fail         :  1;  /* ALT_NAND_STAT_INTR_EN1_PROGRAM_FAIL */
    uint32_t  erase_fail           :  1;  /* ALT_NAND_STAT_INTR_EN1_ERASE_FAIL */
    uint32_t  load_comp            :  1;  /* ALT_NAND_STAT_INTR_EN1_LD_COMP */
    uint32_t  program_comp         :  1;  /* ALT_NAND_STAT_INTR_EN1_PROGRAM_COMP */
    uint32_t  erase_comp           :  1;  /* ALT_NAND_STAT_INTR_EN1_ERASE_COMP */
    uint32_t  pipe_cpybck_cmd_comp :  1;  /* ALT_NAND_STAT_INTR_EN1_PIPE_CPYBCK_CMD_COMP */
    uint32_t  locked_blk           :  1;  /* ALT_NAND_STAT_INTR_EN1_LOCKED_BLK */
    uint32_t  unsup_cmd            :  1;  /* ALT_NAND_STAT_INTR_EN1_UNSUP_CMD */
    uint32_t  INT_act              :  1;  /* ALT_NAND_STAT_INTR_EN1_INT_ACT */
    uint32_t  rst_comp             :  1;  /* ALT_NAND_STAT_INTR_EN1_RST_COMP */
    uint32_t  pipe_cmd_err         :  1;  /* ALT_NAND_STAT_INTR_EN1_PIPE_CMD_ERR */
    uint32_t  page_xfer_inc        :  1;  /* ALT_NAND_STAT_INTR_EN1_PAGE_XFER_INC */
    uint32_t                       : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_INTR_EN1. */
typedef volatile struct ALT_NAND_STAT_INTR_EN1_s  ALT_NAND_STAT_INTR_EN1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_INTR_EN1 register from the beginning of the component. */
#define ALT_NAND_STAT_INTR_EN1_OFST        0x70

/*
 * Register : page_cnt1
 * 
 * Decrementing page count bank 1
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [7:0]  | R      | 0x0   | ALT_NAND_STAT_PAGE_CNT1_VALUE
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : value
 * 
 * Maintains a decrementing count of the number of pages in the multi-page
 * (pipeline and copyback) command being executed.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_PAGE_CNT1_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT1_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_PAGE_CNT1_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT1_VALUE_MSB        7
/* The width in bits of the ALT_NAND_STAT_PAGE_CNT1_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT1_VALUE_WIDTH      8
/* The mask used to set the ALT_NAND_STAT_PAGE_CNT1_VALUE register field value. */
#define ALT_NAND_STAT_PAGE_CNT1_VALUE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_NAND_STAT_PAGE_CNT1_VALUE register field value. */
#define ALT_NAND_STAT_PAGE_CNT1_VALUE_CLR_MSK    0xffffff00
/* The reset value of the ALT_NAND_STAT_PAGE_CNT1_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT1_VALUE_RESET      0x0
/* Extracts the ALT_NAND_STAT_PAGE_CNT1_VALUE field value from a register. */
#define ALT_NAND_STAT_PAGE_CNT1_VALUE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_NAND_STAT_PAGE_CNT1_VALUE register field value suitable for setting the register. */
#define ALT_NAND_STAT_PAGE_CNT1_VALUE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_PAGE_CNT1.
 */
struct ALT_NAND_STAT_PAGE_CNT1_s
{
    const uint32_t  value :  8;  /* ALT_NAND_STAT_PAGE_CNT1_VALUE */
    uint32_t              : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_PAGE_CNT1. */
typedef volatile struct ALT_NAND_STAT_PAGE_CNT1_s  ALT_NAND_STAT_PAGE_CNT1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_PAGE_CNT1 register from the beginning of the component. */
#define ALT_NAND_STAT_PAGE_CNT1_OFST        0x80

/*
 * Register : err_page_addr1
 * 
 * Erred page address bank 1
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                       
 * :--------|:-------|:------|:-----------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                       
 * 
 */
/*
 * Field : value
 * 
 * Holds the page address that resulted in a failure on program or erase operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE_MSB        15
/* The width in bits of the ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE register field value. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE register field value. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE_RESET      0x0
/* Extracts the ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE field value from a register. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE register field value suitable for setting the register. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_ERR_PAGE_ADDR1.
 */
struct ALT_NAND_STAT_ERR_PAGE_ADDR1_s
{
    const uint32_t  value : 16;  /* ALT_NAND_STAT_ERR_PAGE_ADDR1_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_ERR_PAGE_ADDR1. */
typedef volatile struct ALT_NAND_STAT_ERR_PAGE_ADDR1_s  ALT_NAND_STAT_ERR_PAGE_ADDR1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_ERR_PAGE_ADDR1 register from the beginning of the component. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR1_OFST        0x90

/*
 * Register : err_block_addr1
 * 
 * Erred block address bank 1
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                        
 * :--------|:-------|:------|:------------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : value
 * 
 * Holds the block address that resulted in a failure on program or erase
 * operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE_MSB        15
/* The width in bits of the ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE register field value. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE register field value. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE_RESET      0x0
/* Extracts the ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE field value from a register. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE register field value suitable for setting the register. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_ERR_BLOCK_ADDR1.
 */
struct ALT_NAND_STAT_ERR_BLOCK_ADDR1_s
{
    const uint32_t  value : 16;  /* ALT_NAND_STAT_ERR_BLOCK_ADDR1_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_ERR_BLOCK_ADDR1. */
typedef volatile struct ALT_NAND_STAT_ERR_BLOCK_ADDR1_s  ALT_NAND_STAT_ERR_BLOCK_ADDR1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_ERR_BLOCK_ADDR1 register from the beginning of the component. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR1_OFST        0xa0

/*
 * Register : intr_status2
 * 
 * Interrupt status register for bank 2
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                  
 * :--------|:-------|:------|:----------------------------------------------
 *  [0]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR       
 *  [1]     | ???    | 0x0   | *UNDEFINED*                                  
 *  [2]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP        
 *  [3]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_TIME_OUT            
 *  [4]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL        
 *  [5]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL          
 *  [6]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_LD_COMP             
 *  [7]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP        
 *  [8]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_ERASE_COMP          
 *  [9]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP
 *  [10]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK          
 *  [11]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD           
 *  [12]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_INT_ACT             
 *  [13]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_RST_COMP            
 *  [14]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR        
 *  [15]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC       
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                                  
 * 
 */
/*
 * Field : ecc_uncor_err
 * 
 * Ecc logic detected uncorrectable error while reading data from flash device.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR_MSB        0
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : dma_cmd_comp
 * 
 * Not implemented.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP_MSB        2
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP_SET_MSK    0x00000004
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP_CLR_MSK    0xfffffffb
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : time_out
 * 
 * Watchdog timer has triggered in the controller due to one of the reasons like
 * device not responding or controller state machine did not get back to idle
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT2_TIME_OUT_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT2_TIME_OUT_MSB        3
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT2_TIME_OUT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_STAT2_TIME_OUT_SET_MSK    0x00000008
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_STAT2_TIME_OUT_CLR_MSK    0xfffffff7
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT2_TIME_OUT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_TIME_OUT field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_TIME_OUT_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_NAND_STAT_INTR_STAT2_TIME_OUT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_TIME_OUT_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : program_fail
 * 
 * Program failure occurred in the device on issuance of a program command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed program operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL_MSB        4
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL_SET_MSK    0x00000010
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL_CLR_MSK    0xffffffef
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : erase_fail
 * 
 * Erase failure occurred in the device on issuance of a erase command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed erase operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL_MSB        5
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL_SET_MSK    0x00000020
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL_CLR_MSK    0xffffffdf
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : load_comp
 * 
 * Device finished the last issued load command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_LD_COMP_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_LD_COMP_MSB        6
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_LD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT2_LD_COMP_SET_MSK    0x00000040
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT2_LD_COMP_CLR_MSK    0xffffffbf
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_LD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_LD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_LD_COMP_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_NAND_STAT_INTR_STAT2_LD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_LD_COMP_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : program_comp
 * 
 * Device finished the last issued program command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP_MSB        7
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP_SET_MSK    0x00000080
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP_CLR_MSK    0xffffff7f
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : erase_comp
 * 
 * Device erase operation complete
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_COMP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_COMP_MSB        8
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_COMP_SET_MSK    0x00000100
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_COMP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_ERASE_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_COMP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_NAND_STAT_INTR_STAT2_ERASE_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_ERASE_COMP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : pipe_cpybck_cmd_comp
 * 
 * A pipeline command or a copyback bank command has completed on this particular
 * bank
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP_MSB        9
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP_SET_MSK    0x00000200
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : locked_blk
 * 
 * The address to program or erase operation is to a locked block and the operation
 * failed due to this reason
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK_MSB        10
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK_SET_MSK    0x00000400
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK_CLR_MSK    0xfffffbff
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : unsup_cmd
 * 
 * An unsupported command was received. This interrupt is set when an invalid
 * command is received, or when a command sequence is broken.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD_MSB        11
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD_SET_MSK    0x00000800
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : INT_act
 * 
 * R/B pin of device transitioned from low to high
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT2_INT_ACT_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT2_INT_ACT_MSB        12
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT2_INT_ACT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_STAT2_INT_ACT_SET_MSK    0x00001000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_STAT2_INT_ACT_CLR_MSK    0xffffefff
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT2_INT_ACT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_INT_ACT field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_INT_ACT_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_NAND_STAT_INTR_STAT2_INT_ACT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_INT_ACT_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : rst_comp
 * 
 * The NAND Flash Memory Controller has completed its reset and initialization
 * process
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_RST_COMP_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_RST_COMP_MSB        13
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_RST_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT2_RST_COMP_SET_MSK    0x00002000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT2_RST_COMP_CLR_MSK    0xffffdfff
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT2_RST_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_RST_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_RST_COMP_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_NAND_STAT_INTR_STAT2_RST_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_RST_COMP_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : pipe_cmd_err
 * 
 * A pipeline command sequence has been violated. This occurs when Map 01 page
 * read/write address does not match the corresponding expected address from the
 * pipeline commands issued earlier.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR_MSB        14
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR_SET_MSK    0x00004000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR_CLR_MSK    0xffffbfff
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : page_xfer_inc
 * 
 * For every page of data transfer to or from the device, this bit will be set.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC_MSB        15
/* The width in bits of the ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC_SET_MSK    0x00008000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC_CLR_MSK    0xffff7fff
/* The reset value of the ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC field value from a register. */
#define ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC_SET(value) (((value) << 15) & 0x00008000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_INTR_STAT2.
 */
struct ALT_NAND_STAT_INTR_STAT2_s
{
    uint32_t  ecc_uncor_err        :  1;  /* ALT_NAND_STAT_INTR_STAT2_ECC_UNCOR_ERR */
    uint32_t                       :  1;  /* *UNDEFINED* */
    uint32_t  dma_cmd_comp         :  1;  /* ALT_NAND_STAT_INTR_STAT2_DMA_CMD_COMP */
    uint32_t  time_out             :  1;  /* ALT_NAND_STAT_INTR_STAT2_TIME_OUT */
    uint32_t  program_fail         :  1;  /* ALT_NAND_STAT_INTR_STAT2_PROGRAM_FAIL */
    uint32_t  erase_fail           :  1;  /* ALT_NAND_STAT_INTR_STAT2_ERASE_FAIL */
    uint32_t  load_comp            :  1;  /* ALT_NAND_STAT_INTR_STAT2_LD_COMP */
    uint32_t  program_comp         :  1;  /* ALT_NAND_STAT_INTR_STAT2_PROGRAM_COMP */
    uint32_t  erase_comp           :  1;  /* ALT_NAND_STAT_INTR_STAT2_ERASE_COMP */
    uint32_t  pipe_cpybck_cmd_comp :  1;  /* ALT_NAND_STAT_INTR_STAT2_PIPE_CPYBCK_CMD_COMP */
    uint32_t  locked_blk           :  1;  /* ALT_NAND_STAT_INTR_STAT2_LOCKED_BLK */
    uint32_t  unsup_cmd            :  1;  /* ALT_NAND_STAT_INTR_STAT2_UNSUP_CMD */
    uint32_t  INT_act              :  1;  /* ALT_NAND_STAT_INTR_STAT2_INT_ACT */
    uint32_t  rst_comp             :  1;  /* ALT_NAND_STAT_INTR_STAT2_RST_COMP */
    uint32_t  pipe_cmd_err         :  1;  /* ALT_NAND_STAT_INTR_STAT2_PIPE_CMD_ERR */
    uint32_t  page_xfer_inc        :  1;  /* ALT_NAND_STAT_INTR_STAT2_PAGE_XFER_INC */
    uint32_t                       : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_INTR_STAT2. */
typedef volatile struct ALT_NAND_STAT_INTR_STAT2_s  ALT_NAND_STAT_INTR_STAT2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_INTR_STAT2 register from the beginning of the component. */
#define ALT_NAND_STAT_INTR_STAT2_OFST        0xb0

/*
 * Register : intr_en2
 * 
 * Enables corresponding interrupt bit in interrupt register for bank 2
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                
 * :--------|:-------|:------|:--------------------------------------------
 *  [0]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR       
 *  [1]     | ???    | 0x0   | *UNDEFINED*                                
 *  [2]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP        
 *  [3]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN2_TIME_OUT            
 *  [4]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL        
 *  [5]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN2_ERASE_FAIL          
 *  [6]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN2_LD_COMP             
 *  [7]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP        
 *  [8]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN2_ERASE_COMP          
 *  [9]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP
 *  [10]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN2_LOCKED_BLK          
 *  [11]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN2_UNSUP_CMD           
 *  [12]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN2_INT_ACT             
 *  [13]    | RW     | 0x1   | ALT_NAND_STAT_INTR_EN2_RST_COMP            
 *  [14]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR        
 *  [15]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC       
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                                
 * 
 */
/*
 * Field : ecc_uncor_err
 * 
 * If set, Controller will interrupt processor when Ecc logic detects uncorrectable
 * error.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR_MSB        0
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : dma_cmd_comp
 * 
 * Not implemented.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP_MSB        2
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP_SET_MSK    0x00000004
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP_CLR_MSK    0xfffffffb
/* The reset value of the ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : time_out
 * 
 * Watchdog timer has triggered in the controller due to one of the reasons like
 * device not responding or controller state machine did not get back to idle
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN2_TIME_OUT_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN2_TIME_OUT_MSB        3
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN2_TIME_OUT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_EN2_TIME_OUT_SET_MSK    0x00000008
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_EN2_TIME_OUT_CLR_MSK    0xfffffff7
/* The reset value of the ALT_NAND_STAT_INTR_EN2_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN2_TIME_OUT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN2_TIME_OUT field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_TIME_OUT_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_NAND_STAT_INTR_EN2_TIME_OUT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_TIME_OUT_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : program_fail
 * 
 * Program failure occurred in the device on issuance of a program command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed program operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL_MSB        4
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL_SET_MSK    0x00000010
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL_CLR_MSK    0xffffffef
/* The reset value of the ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : erase_fail
 * 
 * Erase failure occurred in the device on issuance of a erase command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed erase operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_FAIL_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_FAIL_MSB        5
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_FAIL_SET_MSK    0x00000020
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_FAIL_CLR_MSK    0xffffffdf
/* The reset value of the ALT_NAND_STAT_INTR_EN2_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN2_ERASE_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_FAIL_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_NAND_STAT_INTR_EN2_ERASE_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_FAIL_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : load_comp
 * 
 * Device finished the last issued load command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_LD_COMP_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_LD_COMP_MSB        6
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_LD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN2_LD_COMP_SET_MSK    0x00000040
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN2_LD_COMP_CLR_MSK    0xffffffbf
/* The reset value of the ALT_NAND_STAT_INTR_EN2_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_LD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN2_LD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_LD_COMP_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_NAND_STAT_INTR_EN2_LD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_LD_COMP_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : program_comp
 * 
 * Device finished the last issued program command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP_MSB        7
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP_SET_MSK    0x00000080
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP_CLR_MSK    0xffffff7f
/* The reset value of the ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : erase_comp
 * 
 * Device erase operation complete
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_COMP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_COMP_MSB        8
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_COMP_SET_MSK    0x00000100
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_COMP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_NAND_STAT_INTR_EN2_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN2_ERASE_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_COMP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_NAND_STAT_INTR_EN2_ERASE_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_ERASE_COMP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : pipe_cpybck_cmd_comp
 * 
 * A pipeline command or a copyback bank command has completed on this particular
 * bank
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP_MSB        9
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP_SET_MSK    0x00000200
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : locked_blk
 * 
 * The address to program or erase operation is to a locked block and the operation
 * failed due to this reason
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN2_LOCKED_BLK_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN2_LOCKED_BLK_MSB        10
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN2_LOCKED_BLK_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_EN2_LOCKED_BLK_SET_MSK    0x00000400
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_EN2_LOCKED_BLK_CLR_MSK    0xfffffbff
/* The reset value of the ALT_NAND_STAT_INTR_EN2_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN2_LOCKED_BLK_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN2_LOCKED_BLK field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_LOCKED_BLK_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_NAND_STAT_INTR_EN2_LOCKED_BLK register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_LOCKED_BLK_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : unsup_cmd
 * 
 * An unsupported command was received. This interrupt is set when an invalid
 * command is received, or when a command sequence is broken.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN2_UNSUP_CMD_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN2_UNSUP_CMD_MSB        11
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN2_UNSUP_CMD_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_EN2_UNSUP_CMD_SET_MSK    0x00000800
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_EN2_UNSUP_CMD_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_NAND_STAT_INTR_EN2_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN2_UNSUP_CMD_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN2_UNSUP_CMD field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_UNSUP_CMD_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_NAND_STAT_INTR_EN2_UNSUP_CMD register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_UNSUP_CMD_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : INT_act
 * 
 * R/B pin of device transitioned from low to high
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN2_INT_ACT_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN2_INT_ACT_MSB        12
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN2_INT_ACT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_EN2_INT_ACT_SET_MSK    0x00001000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_EN2_INT_ACT_CLR_MSK    0xffffefff
/* The reset value of the ALT_NAND_STAT_INTR_EN2_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN2_INT_ACT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN2_INT_ACT field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_INT_ACT_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_NAND_STAT_INTR_EN2_INT_ACT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_INT_ACT_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : rst_comp
 * 
 * A reset command has completed on this bank
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_RST_COMP_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_RST_COMP_MSB        13
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_RST_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN2_RST_COMP_SET_MSK    0x00002000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN2_RST_COMP_CLR_MSK    0xffffdfff
/* The reset value of the ALT_NAND_STAT_INTR_EN2_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN2_RST_COMP_RESET      0x1
/* Extracts the ALT_NAND_STAT_INTR_EN2_RST_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_RST_COMP_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_NAND_STAT_INTR_EN2_RST_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_RST_COMP_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : pipe_cmd_err
 * 
 * A pipeline command sequence has been violated. This occurs when Map 01 page
 * read/write address does not match the corresponding expected address from the
 * pipeline commands issued earlier.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR_MSB        14
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR_SET_MSK    0x00004000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR_CLR_MSK    0xffffbfff
/* The reset value of the ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : page_xfer_inc
 * 
 * For every page of data transfer to or from the device, this bit will be set.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC_MSB        15
/* The width in bits of the ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC_SET_MSK    0x00008000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC_CLR_MSK    0xffff7fff
/* The reset value of the ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC field value from a register. */
#define ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC_SET(value) (((value) << 15) & 0x00008000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_INTR_EN2.
 */
struct ALT_NAND_STAT_INTR_EN2_s
{
    uint32_t  ecc_uncor_err        :  1;  /* ALT_NAND_STAT_INTR_EN2_ECC_UNCOR_ERR */
    uint32_t                       :  1;  /* *UNDEFINED* */
    uint32_t  dma_cmd_comp         :  1;  /* ALT_NAND_STAT_INTR_EN2_DMA_CMD_COMP */
    uint32_t  time_out             :  1;  /* ALT_NAND_STAT_INTR_EN2_TIME_OUT */
    uint32_t  program_fail         :  1;  /* ALT_NAND_STAT_INTR_EN2_PROGRAM_FAIL */
    uint32_t  erase_fail           :  1;  /* ALT_NAND_STAT_INTR_EN2_ERASE_FAIL */
    uint32_t  load_comp            :  1;  /* ALT_NAND_STAT_INTR_EN2_LD_COMP */
    uint32_t  program_comp         :  1;  /* ALT_NAND_STAT_INTR_EN2_PROGRAM_COMP */
    uint32_t  erase_comp           :  1;  /* ALT_NAND_STAT_INTR_EN2_ERASE_COMP */
    uint32_t  pipe_cpybck_cmd_comp :  1;  /* ALT_NAND_STAT_INTR_EN2_PIPE_CPYBCK_CMD_COMP */
    uint32_t  locked_blk           :  1;  /* ALT_NAND_STAT_INTR_EN2_LOCKED_BLK */
    uint32_t  unsup_cmd            :  1;  /* ALT_NAND_STAT_INTR_EN2_UNSUP_CMD */
    uint32_t  INT_act              :  1;  /* ALT_NAND_STAT_INTR_EN2_INT_ACT */
    uint32_t  rst_comp             :  1;  /* ALT_NAND_STAT_INTR_EN2_RST_COMP */
    uint32_t  pipe_cmd_err         :  1;  /* ALT_NAND_STAT_INTR_EN2_PIPE_CMD_ERR */
    uint32_t  page_xfer_inc        :  1;  /* ALT_NAND_STAT_INTR_EN2_PAGE_XFER_INC */
    uint32_t                       : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_INTR_EN2. */
typedef volatile struct ALT_NAND_STAT_INTR_EN2_s  ALT_NAND_STAT_INTR_EN2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_INTR_EN2 register from the beginning of the component. */
#define ALT_NAND_STAT_INTR_EN2_OFST        0xc0

/*
 * Register : page_cnt2
 * 
 * Decrementing page count bank 2
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [7:0]  | R      | 0x0   | ALT_NAND_STAT_PAGE_CNT2_VALUE
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : value
 * 
 * Maintains a decrementing count of the number of pages in the multi-page
 * (pipeline and copyback) command being executed.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_PAGE_CNT2_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT2_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_PAGE_CNT2_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT2_VALUE_MSB        7
/* The width in bits of the ALT_NAND_STAT_PAGE_CNT2_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT2_VALUE_WIDTH      8
/* The mask used to set the ALT_NAND_STAT_PAGE_CNT2_VALUE register field value. */
#define ALT_NAND_STAT_PAGE_CNT2_VALUE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_NAND_STAT_PAGE_CNT2_VALUE register field value. */
#define ALT_NAND_STAT_PAGE_CNT2_VALUE_CLR_MSK    0xffffff00
/* The reset value of the ALT_NAND_STAT_PAGE_CNT2_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT2_VALUE_RESET      0x0
/* Extracts the ALT_NAND_STAT_PAGE_CNT2_VALUE field value from a register. */
#define ALT_NAND_STAT_PAGE_CNT2_VALUE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_NAND_STAT_PAGE_CNT2_VALUE register field value suitable for setting the register. */
#define ALT_NAND_STAT_PAGE_CNT2_VALUE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_PAGE_CNT2.
 */
struct ALT_NAND_STAT_PAGE_CNT2_s
{
    const uint32_t  value :  8;  /* ALT_NAND_STAT_PAGE_CNT2_VALUE */
    uint32_t              : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_PAGE_CNT2. */
typedef volatile struct ALT_NAND_STAT_PAGE_CNT2_s  ALT_NAND_STAT_PAGE_CNT2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_PAGE_CNT2 register from the beginning of the component. */
#define ALT_NAND_STAT_PAGE_CNT2_OFST        0xd0

/*
 * Register : err_page_addr2
 * 
 * Erred page address bank 2
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                       
 * :--------|:-------|:------|:-----------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                       
 * 
 */
/*
 * Field : value
 * 
 * Holds the page address that resulted in a failure on program or erase operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE_MSB        15
/* The width in bits of the ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE register field value. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE register field value. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE_RESET      0x0
/* Extracts the ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE field value from a register. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE register field value suitable for setting the register. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_ERR_PAGE_ADDR2.
 */
struct ALT_NAND_STAT_ERR_PAGE_ADDR2_s
{
    const uint32_t  value : 16;  /* ALT_NAND_STAT_ERR_PAGE_ADDR2_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_ERR_PAGE_ADDR2. */
typedef volatile struct ALT_NAND_STAT_ERR_PAGE_ADDR2_s  ALT_NAND_STAT_ERR_PAGE_ADDR2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_ERR_PAGE_ADDR2 register from the beginning of the component. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR2_OFST        0xe0

/*
 * Register : err_block_addr2
 * 
 * Erred block address bank 2
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                        
 * :--------|:-------|:------|:------------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : value
 * 
 * Holds the block address that resulted in a failure on program or erase
 * operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE_MSB        15
/* The width in bits of the ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE register field value. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE register field value. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE_RESET      0x0
/* Extracts the ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE field value from a register. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE register field value suitable for setting the register. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_ERR_BLOCK_ADDR2.
 */
struct ALT_NAND_STAT_ERR_BLOCK_ADDR2_s
{
    const uint32_t  value : 16;  /* ALT_NAND_STAT_ERR_BLOCK_ADDR2_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_ERR_BLOCK_ADDR2. */
typedef volatile struct ALT_NAND_STAT_ERR_BLOCK_ADDR2_s  ALT_NAND_STAT_ERR_BLOCK_ADDR2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_ERR_BLOCK_ADDR2 register from the beginning of the component. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR2_OFST        0xf0

/*
 * Register : intr_status3
 * 
 * Interrupt status register for bank 3
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                  
 * :--------|:-------|:------|:----------------------------------------------
 *  [0]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR       
 *  [1]     | ???    | 0x0   | *UNDEFINED*                                  
 *  [2]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP        
 *  [3]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_TIME_OUT            
 *  [4]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL        
 *  [5]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL          
 *  [6]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_LD_COMP             
 *  [7]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP        
 *  [8]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_ERASE_COMP          
 *  [9]     | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP
 *  [10]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK          
 *  [11]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD           
 *  [12]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_INT_ACT             
 *  [13]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_RST_COMP            
 *  [14]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR        
 *  [15]    | RW     | 0x0   | ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC       
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                                  
 * 
 */
/*
 * Field : ecc_uncor_err
 * 
 * Ecc logic detected uncorrectable error while reading data from flash device.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR_MSB        0
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : dma_cmd_comp
 * 
 * Not implemented.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP_MSB        2
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP_SET_MSK    0x00000004
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP_CLR_MSK    0xfffffffb
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : time_out
 * 
 * Watchdog timer has triggered in the controller due to one of the reasons like
 * device not responding or controller state machine did not get back to idle
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT3_TIME_OUT_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT3_TIME_OUT_MSB        3
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT3_TIME_OUT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_STAT3_TIME_OUT_SET_MSK    0x00000008
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_STAT3_TIME_OUT_CLR_MSK    0xfffffff7
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_STAT3_TIME_OUT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_TIME_OUT field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_TIME_OUT_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_NAND_STAT_INTR_STAT3_TIME_OUT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_TIME_OUT_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : program_fail
 * 
 * Program failure occurred in the device on issuance of a program command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed program operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL_MSB        4
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL_SET_MSK    0x00000010
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL_CLR_MSK    0xffffffef
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : erase_fail
 * 
 * Erase failure occurred in the device on issuance of a erase command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed erase operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL_MSB        5
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL_SET_MSK    0x00000020
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL_CLR_MSK    0xffffffdf
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : load_comp
 * 
 * Device finished the last issued load command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_LD_COMP_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_LD_COMP_MSB        6
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_LD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT3_LD_COMP_SET_MSK    0x00000040
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT3_LD_COMP_CLR_MSK    0xffffffbf
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_LD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_LD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_LD_COMP_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_NAND_STAT_INTR_STAT3_LD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_LD_COMP_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : program_comp
 * 
 * Device finished the last issued program command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP_MSB        7
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP_SET_MSK    0x00000080
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP_CLR_MSK    0xffffff7f
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : erase_comp
 * 
 * Device erase operation complete
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_COMP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_COMP_MSB        8
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_COMP_SET_MSK    0x00000100
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_COMP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_ERASE_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_COMP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_NAND_STAT_INTR_STAT3_ERASE_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_ERASE_COMP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : pipe_cpybck_cmd_comp
 * 
 * A pipeline command or a copyback bank command has completed on this particular
 * bank
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP_MSB        9
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP_SET_MSK    0x00000200
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : locked_blk
 * 
 * The address to program or erase operation is to a locked block and the operation
 * failed due to this reason
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK_MSB        10
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK_SET_MSK    0x00000400
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK_CLR_MSK    0xfffffbff
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : unsup_cmd
 * 
 * An unsupported command was received. This interrupt is set when an invalid
 * command is received, or when a command sequence is broken.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD_MSB        11
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD_SET_MSK    0x00000800
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : INT_act
 * 
 * R/B pin of device transitioned from low to high
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT3_INT_ACT_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT3_INT_ACT_MSB        12
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT3_INT_ACT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_STAT3_INT_ACT_SET_MSK    0x00001000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_STAT3_INT_ACT_CLR_MSK    0xffffefff
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_STAT3_INT_ACT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_INT_ACT field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_INT_ACT_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_NAND_STAT_INTR_STAT3_INT_ACT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_INT_ACT_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : rst_comp
 * 
 * The NAND Flash Memory Controller has completed its reset and initialization
 * process
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_RST_COMP_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_RST_COMP_MSB        13
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_RST_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT3_RST_COMP_SET_MSK    0x00002000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_STAT3_RST_COMP_CLR_MSK    0xffffdfff
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_STAT3_RST_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_RST_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_RST_COMP_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_NAND_STAT_INTR_STAT3_RST_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_RST_COMP_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : pipe_cmd_err
 * 
 * A pipeline command sequence has been violated. This occurs when Map 01 page
 * read/write address does not match the corresponding expected address from the
 * pipeline commands issued earlier.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR_MSB        14
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR_SET_MSK    0x00004000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR_CLR_MSK    0xffffbfff
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : page_xfer_inc
 * 
 * For every page of data transfer to or from the device, this bit will be set.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC_MSB        15
/* The width in bits of the ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC_SET_MSK    0x00008000
/* The mask used to clear the ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC_CLR_MSK    0xffff7fff
/* The reset value of the ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC field value from a register. */
#define ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC_SET(value) (((value) << 15) & 0x00008000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_INTR_STAT3.
 */
struct ALT_NAND_STAT_INTR_STAT3_s
{
    uint32_t  ecc_uncor_err        :  1;  /* ALT_NAND_STAT_INTR_STAT3_ECC_UNCOR_ERR */
    uint32_t                       :  1;  /* *UNDEFINED* */
    uint32_t  dma_cmd_comp         :  1;  /* ALT_NAND_STAT_INTR_STAT3_DMA_CMD_COMP */
    uint32_t  time_out             :  1;  /* ALT_NAND_STAT_INTR_STAT3_TIME_OUT */
    uint32_t  program_fail         :  1;  /* ALT_NAND_STAT_INTR_STAT3_PROGRAM_FAIL */
    uint32_t  erase_fail           :  1;  /* ALT_NAND_STAT_INTR_STAT3_ERASE_FAIL */
    uint32_t  load_comp            :  1;  /* ALT_NAND_STAT_INTR_STAT3_LD_COMP */
    uint32_t  program_comp         :  1;  /* ALT_NAND_STAT_INTR_STAT3_PROGRAM_COMP */
    uint32_t  erase_comp           :  1;  /* ALT_NAND_STAT_INTR_STAT3_ERASE_COMP */
    uint32_t  pipe_cpybck_cmd_comp :  1;  /* ALT_NAND_STAT_INTR_STAT3_PIPE_CPYBCK_CMD_COMP */
    uint32_t  locked_blk           :  1;  /* ALT_NAND_STAT_INTR_STAT3_LOCKED_BLK */
    uint32_t  unsup_cmd            :  1;  /* ALT_NAND_STAT_INTR_STAT3_UNSUP_CMD */
    uint32_t  INT_act              :  1;  /* ALT_NAND_STAT_INTR_STAT3_INT_ACT */
    uint32_t  rst_comp             :  1;  /* ALT_NAND_STAT_INTR_STAT3_RST_COMP */
    uint32_t  pipe_cmd_err         :  1;  /* ALT_NAND_STAT_INTR_STAT3_PIPE_CMD_ERR */
    uint32_t  page_xfer_inc        :  1;  /* ALT_NAND_STAT_INTR_STAT3_PAGE_XFER_INC */
    uint32_t                       : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_INTR_STAT3. */
typedef volatile struct ALT_NAND_STAT_INTR_STAT3_s  ALT_NAND_STAT_INTR_STAT3_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_INTR_STAT3 register from the beginning of the component. */
#define ALT_NAND_STAT_INTR_STAT3_OFST        0x100

/*
 * Register : intr_en3
 * 
 * Enables corresponding interrupt bit in interrupt register for bank 3
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                                
 * :--------|:-------|:------|:--------------------------------------------
 *  [0]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR       
 *  [1]     | ???    | 0x0   | *UNDEFINED*                                
 *  [2]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP        
 *  [3]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN3_TIME_OUT            
 *  [4]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL        
 *  [5]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN3_ERASE_FAIL          
 *  [6]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN3_LD_COMP             
 *  [7]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP        
 *  [8]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN3_ERASE_COMP          
 *  [9]     | RW     | 0x0   | ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP
 *  [10]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN3_LOCKED_BLK          
 *  [11]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN3_UNSUP_CMD           
 *  [12]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN3_INT_ACT             
 *  [13]    | RW     | 0x1   | ALT_NAND_STAT_INTR_EN3_RST_COMP            
 *  [14]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR        
 *  [15]    | RW     | 0x0   | ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC       
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                                
 * 
 */
/*
 * Field : ecc_uncor_err
 * 
 * If set, Controller will interrupt processor when Ecc logic detects uncorrectable
 * error.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR_MSB        0
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR register field. */
#define ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : dma_cmd_comp
 * 
 * Not implemented.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP_MSB        2
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP_SET_MSK    0x00000004
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP_CLR_MSK    0xfffffffb
/* The reset value of the ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : time_out
 * 
 * Watchdog timer has triggered in the controller due to one of the reasons like
 * device not responding or controller state machine did not get back to idle
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN3_TIME_OUT_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN3_TIME_OUT_MSB        3
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN3_TIME_OUT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_EN3_TIME_OUT_SET_MSK    0x00000008
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_TIME_OUT register field value. */
#define ALT_NAND_STAT_INTR_EN3_TIME_OUT_CLR_MSK    0xfffffff7
/* The reset value of the ALT_NAND_STAT_INTR_EN3_TIME_OUT register field. */
#define ALT_NAND_STAT_INTR_EN3_TIME_OUT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN3_TIME_OUT field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_TIME_OUT_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_NAND_STAT_INTR_EN3_TIME_OUT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_TIME_OUT_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : program_fail
 * 
 * Program failure occurred in the device on issuance of a program command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed program operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL_MSB        4
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL_SET_MSK    0x00000010
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL_CLR_MSK    0xffffffef
/* The reset value of the ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : erase_fail
 * 
 * Erase failure occurred in the device on issuance of a erase command.
 * err_block_addr and err_page_addr contain the block address and page address that
 * failed erase operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_FAIL_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_FAIL_MSB        5
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_FAIL_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_FAIL_SET_MSK    0x00000020
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_ERASE_FAIL register field value. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_FAIL_CLR_MSK    0xffffffdf
/* The reset value of the ALT_NAND_STAT_INTR_EN3_ERASE_FAIL register field. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_FAIL_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN3_ERASE_FAIL field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_FAIL_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_NAND_STAT_INTR_EN3_ERASE_FAIL register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_FAIL_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : load_comp
 * 
 * Device finished the last issued load command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_LD_COMP_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_LD_COMP_MSB        6
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_LD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN3_LD_COMP_SET_MSK    0x00000040
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_LD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN3_LD_COMP_CLR_MSK    0xffffffbf
/* The reset value of the ALT_NAND_STAT_INTR_EN3_LD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_LD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN3_LD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_LD_COMP_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_NAND_STAT_INTR_EN3_LD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_LD_COMP_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : program_comp
 * 
 * Device finished the last issued program command.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP_MSB        7
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP_SET_MSK    0x00000080
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP_CLR_MSK    0xffffff7f
/* The reset value of the ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : erase_comp
 * 
 * Device erase operation complete
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_COMP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_COMP_MSB        8
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_COMP_SET_MSK    0x00000100
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_ERASE_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_COMP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_NAND_STAT_INTR_EN3_ERASE_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN3_ERASE_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_COMP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_NAND_STAT_INTR_EN3_ERASE_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_ERASE_COMP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : pipe_cpybck_cmd_comp
 * 
 * A pipeline command or a copyback bank command has completed on this particular
 * bank
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP_MSB        9
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP_SET_MSK    0x00000200
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : locked_blk
 * 
 * The address to program or erase operation is to a locked block and the operation
 * failed due to this reason
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN3_LOCKED_BLK_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN3_LOCKED_BLK_MSB        10
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN3_LOCKED_BLK_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_EN3_LOCKED_BLK_SET_MSK    0x00000400
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_LOCKED_BLK register field value. */
#define ALT_NAND_STAT_INTR_EN3_LOCKED_BLK_CLR_MSK    0xfffffbff
/* The reset value of the ALT_NAND_STAT_INTR_EN3_LOCKED_BLK register field. */
#define ALT_NAND_STAT_INTR_EN3_LOCKED_BLK_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN3_LOCKED_BLK field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_LOCKED_BLK_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_NAND_STAT_INTR_EN3_LOCKED_BLK register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_LOCKED_BLK_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : unsup_cmd
 * 
 * An unsupported command was received. This interrupt is set when an invalid
 * command is received, or when a command sequence is broken.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN3_UNSUP_CMD_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN3_UNSUP_CMD_MSB        11
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN3_UNSUP_CMD_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_EN3_UNSUP_CMD_SET_MSK    0x00000800
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_UNSUP_CMD register field value. */
#define ALT_NAND_STAT_INTR_EN3_UNSUP_CMD_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_NAND_STAT_INTR_EN3_UNSUP_CMD register field. */
#define ALT_NAND_STAT_INTR_EN3_UNSUP_CMD_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN3_UNSUP_CMD field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_UNSUP_CMD_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_NAND_STAT_INTR_EN3_UNSUP_CMD register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_UNSUP_CMD_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : INT_act
 * 
 * R/B pin of device transitioned from low to high
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN3_INT_ACT_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN3_INT_ACT_MSB        12
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN3_INT_ACT_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_EN3_INT_ACT_SET_MSK    0x00001000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_INT_ACT register field value. */
#define ALT_NAND_STAT_INTR_EN3_INT_ACT_CLR_MSK    0xffffefff
/* The reset value of the ALT_NAND_STAT_INTR_EN3_INT_ACT register field. */
#define ALT_NAND_STAT_INTR_EN3_INT_ACT_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN3_INT_ACT field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_INT_ACT_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_NAND_STAT_INTR_EN3_INT_ACT register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_INT_ACT_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : rst_comp
 * 
 * A reset command has completed on this bank
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_RST_COMP_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_RST_COMP_MSB        13
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_RST_COMP_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN3_RST_COMP_SET_MSK    0x00002000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_RST_COMP register field value. */
#define ALT_NAND_STAT_INTR_EN3_RST_COMP_CLR_MSK    0xffffdfff
/* The reset value of the ALT_NAND_STAT_INTR_EN3_RST_COMP register field. */
#define ALT_NAND_STAT_INTR_EN3_RST_COMP_RESET      0x1
/* Extracts the ALT_NAND_STAT_INTR_EN3_RST_COMP field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_RST_COMP_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_NAND_STAT_INTR_EN3_RST_COMP register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_RST_COMP_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : pipe_cmd_err
 * 
 * A pipeline command sequence has been violated. This occurs when Map 01 page
 * read/write address does not match the corresponding expected address from the
 * pipeline commands issued earlier.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR_MSB        14
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR_SET_MSK    0x00004000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR register field value. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR_CLR_MSK    0xffffbfff
/* The reset value of the ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR register field. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : page_xfer_inc
 * 
 * For every page of data transfer to or from the device, this bit will be set.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC_MSB        15
/* The width in bits of the ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC_WIDTH      1
/* The mask used to set the ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC_SET_MSK    0x00008000
/* The mask used to clear the ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC register field value. */
#define ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC_CLR_MSK    0xffff7fff
/* The reset value of the ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC register field. */
#define ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC_RESET      0x0
/* Extracts the ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC field value from a register. */
#define ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC register field value suitable for setting the register. */
#define ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC_SET(value) (((value) << 15) & 0x00008000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_INTR_EN3.
 */
struct ALT_NAND_STAT_INTR_EN3_s
{
    uint32_t  ecc_uncor_err        :  1;  /* ALT_NAND_STAT_INTR_EN3_ECC_UNCOR_ERR */
    uint32_t                       :  1;  /* *UNDEFINED* */
    uint32_t  dma_cmd_comp         :  1;  /* ALT_NAND_STAT_INTR_EN3_DMA_CMD_COMP */
    uint32_t  time_out             :  1;  /* ALT_NAND_STAT_INTR_EN3_TIME_OUT */
    uint32_t  program_fail         :  1;  /* ALT_NAND_STAT_INTR_EN3_PROGRAM_FAIL */
    uint32_t  erase_fail           :  1;  /* ALT_NAND_STAT_INTR_EN3_ERASE_FAIL */
    uint32_t  load_comp            :  1;  /* ALT_NAND_STAT_INTR_EN3_LD_COMP */
    uint32_t  program_comp         :  1;  /* ALT_NAND_STAT_INTR_EN3_PROGRAM_COMP */
    uint32_t  erase_comp           :  1;  /* ALT_NAND_STAT_INTR_EN3_ERASE_COMP */
    uint32_t  pipe_cpybck_cmd_comp :  1;  /* ALT_NAND_STAT_INTR_EN3_PIPE_CPYBCK_CMD_COMP */
    uint32_t  locked_blk           :  1;  /* ALT_NAND_STAT_INTR_EN3_LOCKED_BLK */
    uint32_t  unsup_cmd            :  1;  /* ALT_NAND_STAT_INTR_EN3_UNSUP_CMD */
    uint32_t  INT_act              :  1;  /* ALT_NAND_STAT_INTR_EN3_INT_ACT */
    uint32_t  rst_comp             :  1;  /* ALT_NAND_STAT_INTR_EN3_RST_COMP */
    uint32_t  pipe_cmd_err         :  1;  /* ALT_NAND_STAT_INTR_EN3_PIPE_CMD_ERR */
    uint32_t  page_xfer_inc        :  1;  /* ALT_NAND_STAT_INTR_EN3_PAGE_XFER_INC */
    uint32_t                       : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_INTR_EN3. */
typedef volatile struct ALT_NAND_STAT_INTR_EN3_s  ALT_NAND_STAT_INTR_EN3_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_INTR_EN3 register from the beginning of the component. */
#define ALT_NAND_STAT_INTR_EN3_OFST        0x110

/*
 * Register : page_cnt3
 * 
 * Decrementing page count bank 3
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [7:0]  | R      | 0x0   | ALT_NAND_STAT_PAGE_CNT3_VALUE
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : value
 * 
 * Maintains a decrementing count of the number of pages in the multi-page
 * (pipeline and copyback) command being executed.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_PAGE_CNT3_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT3_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_PAGE_CNT3_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT3_VALUE_MSB        7
/* The width in bits of the ALT_NAND_STAT_PAGE_CNT3_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT3_VALUE_WIDTH      8
/* The mask used to set the ALT_NAND_STAT_PAGE_CNT3_VALUE register field value. */
#define ALT_NAND_STAT_PAGE_CNT3_VALUE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_NAND_STAT_PAGE_CNT3_VALUE register field value. */
#define ALT_NAND_STAT_PAGE_CNT3_VALUE_CLR_MSK    0xffffff00
/* The reset value of the ALT_NAND_STAT_PAGE_CNT3_VALUE register field. */
#define ALT_NAND_STAT_PAGE_CNT3_VALUE_RESET      0x0
/* Extracts the ALT_NAND_STAT_PAGE_CNT3_VALUE field value from a register. */
#define ALT_NAND_STAT_PAGE_CNT3_VALUE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_NAND_STAT_PAGE_CNT3_VALUE register field value suitable for setting the register. */
#define ALT_NAND_STAT_PAGE_CNT3_VALUE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_PAGE_CNT3.
 */
struct ALT_NAND_STAT_PAGE_CNT3_s
{
    const uint32_t  value :  8;  /* ALT_NAND_STAT_PAGE_CNT3_VALUE */
    uint32_t              : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_PAGE_CNT3. */
typedef volatile struct ALT_NAND_STAT_PAGE_CNT3_s  ALT_NAND_STAT_PAGE_CNT3_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_PAGE_CNT3 register from the beginning of the component. */
#define ALT_NAND_STAT_PAGE_CNT3_OFST        0x120

/*
 * Register : err_page_addr3
 * 
 * Erred page address bank 3
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                       
 * :--------|:-------|:------|:-----------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                       
 * 
 */
/*
 * Field : value
 * 
 * Holds the page address that resulted in a failure on program or erase operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE_MSB        15
/* The width in bits of the ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE register field value. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE register field value. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE register field. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE_RESET      0x0
/* Extracts the ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE field value from a register. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE register field value suitable for setting the register. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_ERR_PAGE_ADDR3.
 */
struct ALT_NAND_STAT_ERR_PAGE_ADDR3_s
{
    const uint32_t  value : 16;  /* ALT_NAND_STAT_ERR_PAGE_ADDR3_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_ERR_PAGE_ADDR3. */
typedef volatile struct ALT_NAND_STAT_ERR_PAGE_ADDR3_s  ALT_NAND_STAT_ERR_PAGE_ADDR3_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_ERR_PAGE_ADDR3 register from the beginning of the component. */
#define ALT_NAND_STAT_ERR_PAGE_ADDR3_OFST        0x130

/*
 * Register : err_block_addr3
 * 
 * Erred block address bank 3
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                        
 * :--------|:-------|:------|:------------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : value
 * 
 * Holds the block address that resulted in a failure on program or erase
 * operation.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE_MSB        15
/* The width in bits of the ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE register field value. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE register field value. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE register field. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE_RESET      0x0
/* Extracts the ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE field value from a register. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE register field value suitable for setting the register. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_STAT_ERR_BLOCK_ADDR3.
 */
struct ALT_NAND_STAT_ERR_BLOCK_ADDR3_s
{
    const uint32_t  value : 16;  /* ALT_NAND_STAT_ERR_BLOCK_ADDR3_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_STAT_ERR_BLOCK_ADDR3. */
typedef volatile struct ALT_NAND_STAT_ERR_BLOCK_ADDR3_s  ALT_NAND_STAT_ERR_BLOCK_ADDR3_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_STAT_ERR_BLOCK_ADDR3 register from the beginning of the component. */
#define ALT_NAND_STAT_ERR_BLOCK_ADDR3_OFST        0x140

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_NAND_STAT.
 */
struct ALT_NAND_STAT_s
{
    volatile ALT_NAND_STAT_TFR_MOD_t          transfer_mode;        /* ALT_NAND_STAT_TFR_MOD */
    volatile uint32_t                         _pad_0x4_0xf[3];      /* *UNDEFINED* */
    volatile ALT_NAND_STAT_INTR_STAT0_t       intr_status0;         /* ALT_NAND_STAT_INTR_STAT0 */
    volatile uint32_t                         _pad_0x14_0x1f[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_INTR_EN0_t         intr_en0;             /* ALT_NAND_STAT_INTR_EN0 */
    volatile uint32_t                         _pad_0x24_0x2f[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_PAGE_CNT0_t        page_cnt0;            /* ALT_NAND_STAT_PAGE_CNT0 */
    volatile uint32_t                         _pad_0x34_0x3f[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_ERR_PAGE_ADDR0_t   err_page_addr0;       /* ALT_NAND_STAT_ERR_PAGE_ADDR0 */
    volatile uint32_t                         _pad_0x44_0x4f[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_ERR_BLOCK_ADDR0_t  err_block_addr0;      /* ALT_NAND_STAT_ERR_BLOCK_ADDR0 */
    volatile uint32_t                         _pad_0x54_0x5f[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_INTR_STAT1_t       intr_status1;         /* ALT_NAND_STAT_INTR_STAT1 */
    volatile uint32_t                         _pad_0x64_0x6f[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_INTR_EN1_t         intr_en1;             /* ALT_NAND_STAT_INTR_EN1 */
    volatile uint32_t                         _pad_0x74_0x7f[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_PAGE_CNT1_t        page_cnt1;            /* ALT_NAND_STAT_PAGE_CNT1 */
    volatile uint32_t                         _pad_0x84_0x8f[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_ERR_PAGE_ADDR1_t   err_page_addr1;       /* ALT_NAND_STAT_ERR_PAGE_ADDR1 */
    volatile uint32_t                         _pad_0x94_0x9f[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_ERR_BLOCK_ADDR1_t  err_block_addr1;      /* ALT_NAND_STAT_ERR_BLOCK_ADDR1 */
    volatile uint32_t                         _pad_0xa4_0xaf[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_INTR_STAT2_t       intr_status2;         /* ALT_NAND_STAT_INTR_STAT2 */
    volatile uint32_t                         _pad_0xb4_0xbf[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_INTR_EN2_t         intr_en2;             /* ALT_NAND_STAT_INTR_EN2 */
    volatile uint32_t                         _pad_0xc4_0xcf[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_PAGE_CNT2_t        page_cnt2;            /* ALT_NAND_STAT_PAGE_CNT2 */
    volatile uint32_t                         _pad_0xd4_0xdf[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_ERR_PAGE_ADDR2_t   err_page_addr2;       /* ALT_NAND_STAT_ERR_PAGE_ADDR2 */
    volatile uint32_t                         _pad_0xe4_0xef[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_ERR_BLOCK_ADDR2_t  err_block_addr2;      /* ALT_NAND_STAT_ERR_BLOCK_ADDR2 */
    volatile uint32_t                         _pad_0xf4_0xff[3];    /* *UNDEFINED* */
    volatile ALT_NAND_STAT_INTR_STAT3_t       intr_status3;         /* ALT_NAND_STAT_INTR_STAT3 */
    volatile uint32_t                         _pad_0x104_0x10f[3];  /* *UNDEFINED* */
    volatile ALT_NAND_STAT_INTR_EN3_t         intr_en3;             /* ALT_NAND_STAT_INTR_EN3 */
    volatile uint32_t                         _pad_0x114_0x11f[3];  /* *UNDEFINED* */
    volatile ALT_NAND_STAT_PAGE_CNT3_t        page_cnt3;            /* ALT_NAND_STAT_PAGE_CNT3 */
    volatile uint32_t                         _pad_0x124_0x12f[3];  /* *UNDEFINED* */
    volatile ALT_NAND_STAT_ERR_PAGE_ADDR3_t   err_page_addr3;       /* ALT_NAND_STAT_ERR_PAGE_ADDR3 */
    volatile uint32_t                         _pad_0x134_0x13f[3];  /* *UNDEFINED* */
    volatile ALT_NAND_STAT_ERR_BLOCK_ADDR3_t  err_block_addr3;      /* ALT_NAND_STAT_ERR_BLOCK_ADDR3 */
};

/* The typedef declaration for register group ALT_NAND_STAT. */
typedef volatile struct ALT_NAND_STAT_s  ALT_NAND_STAT_t;
/* The struct declaration for the raw register contents of register group ALT_NAND_STAT. */
struct ALT_NAND_STAT_raw_s
{
    volatile uint32_t  transfer_mode;        /* ALT_NAND_STAT_TFR_MOD */
    volatile uint32_t  _pad_0x4_0xf[3];      /* *UNDEFINED* */
    volatile uint32_t  intr_status0;         /* ALT_NAND_STAT_INTR_STAT0 */
    volatile uint32_t  _pad_0x14_0x1f[3];    /* *UNDEFINED* */
    volatile uint32_t  intr_en0;             /* ALT_NAND_STAT_INTR_EN0 */
    volatile uint32_t  _pad_0x24_0x2f[3];    /* *UNDEFINED* */
    volatile uint32_t  page_cnt0;            /* ALT_NAND_STAT_PAGE_CNT0 */
    volatile uint32_t  _pad_0x34_0x3f[3];    /* *UNDEFINED* */
    volatile uint32_t  err_page_addr0;       /* ALT_NAND_STAT_ERR_PAGE_ADDR0 */
    volatile uint32_t  _pad_0x44_0x4f[3];    /* *UNDEFINED* */
    volatile uint32_t  err_block_addr0;      /* ALT_NAND_STAT_ERR_BLOCK_ADDR0 */
    volatile uint32_t  _pad_0x54_0x5f[3];    /* *UNDEFINED* */
    volatile uint32_t  intr_status1;         /* ALT_NAND_STAT_INTR_STAT1 */
    volatile uint32_t  _pad_0x64_0x6f[3];    /* *UNDEFINED* */
    volatile uint32_t  intr_en1;             /* ALT_NAND_STAT_INTR_EN1 */
    volatile uint32_t  _pad_0x74_0x7f[3];    /* *UNDEFINED* */
    volatile uint32_t  page_cnt1;            /* ALT_NAND_STAT_PAGE_CNT1 */
    volatile uint32_t  _pad_0x84_0x8f[3];    /* *UNDEFINED* */
    volatile uint32_t  err_page_addr1;       /* ALT_NAND_STAT_ERR_PAGE_ADDR1 */
    volatile uint32_t  _pad_0x94_0x9f[3];    /* *UNDEFINED* */
    volatile uint32_t  err_block_addr1;      /* ALT_NAND_STAT_ERR_BLOCK_ADDR1 */
    volatile uint32_t  _pad_0xa4_0xaf[3];    /* *UNDEFINED* */
    volatile uint32_t  intr_status2;         /* ALT_NAND_STAT_INTR_STAT2 */
    volatile uint32_t  _pad_0xb4_0xbf[3];    /* *UNDEFINED* */
    volatile uint32_t  intr_en2;             /* ALT_NAND_STAT_INTR_EN2 */
    volatile uint32_t  _pad_0xc4_0xcf[3];    /* *UNDEFINED* */
    volatile uint32_t  page_cnt2;            /* ALT_NAND_STAT_PAGE_CNT2 */
    volatile uint32_t  _pad_0xd4_0xdf[3];    /* *UNDEFINED* */
    volatile uint32_t  err_page_addr2;       /* ALT_NAND_STAT_ERR_PAGE_ADDR2 */
    volatile uint32_t  _pad_0xe4_0xef[3];    /* *UNDEFINED* */
    volatile uint32_t  err_block_addr2;      /* ALT_NAND_STAT_ERR_BLOCK_ADDR2 */
    volatile uint32_t  _pad_0xf4_0xff[3];    /* *UNDEFINED* */
    volatile uint32_t  intr_status3;         /* ALT_NAND_STAT_INTR_STAT3 */
    volatile uint32_t  _pad_0x104_0x10f[3];  /* *UNDEFINED* */
    volatile uint32_t  intr_en3;             /* ALT_NAND_STAT_INTR_EN3 */
    volatile uint32_t  _pad_0x114_0x11f[3];  /* *UNDEFINED* */
    volatile uint32_t  page_cnt3;            /* ALT_NAND_STAT_PAGE_CNT3 */
    volatile uint32_t  _pad_0x124_0x12f[3];  /* *UNDEFINED* */
    volatile uint32_t  err_page_addr3;       /* ALT_NAND_STAT_ERR_PAGE_ADDR3 */
    volatile uint32_t  _pad_0x134_0x13f[3];  /* *UNDEFINED* */
    volatile uint32_t  err_block_addr3;      /* ALT_NAND_STAT_ERR_BLOCK_ADDR3 */
};

/* The typedef declaration for the raw register contents of register group ALT_NAND_STAT. */
typedef volatile struct ALT_NAND_STAT_raw_s  ALT_NAND_STAT_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : ECC registers - ALT_NAND_ECC
 * ECC registers
 * 
 * 
 */
/*
 * Register : ECCCorInfo_b01
 * 
 * ECC Error correction Information register. Controller updates this register when
 * it completes a transaction. The values are held in this register till a new
 * transaction completes.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                              
 * :--------|:-------|:------|:------------------------------------------
 *  [6:0]   | R      | 0x0   | ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0
 *  [7]     | R      | 0x0   | ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0 
 *  [14:8]  | R      | 0x0   | ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1
 *  [15]    | R      | 0x0   | ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1 
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                              
 * 
 */
/*
 * Field : max_errors_b0
 * 
 * Maximum of number of errors corrected per sector in Bank0. This field is not
 * valid for uncorrectable errors. A value of zero indicates that no ECC error
 * occurred in last completed transaction.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0_MSB        6
/* The width in bits of the ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0_WIDTH      7
/* The mask used to set the ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0_SET_MSK    0x0000007f
/* The mask used to clear the ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0_CLR_MSK    0xffffff80
/* The reset value of the ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0_RESET      0x0
/* Extracts the ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0 field value from a register. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0_GET(value) (((value) & 0x0000007f) >> 0)
/* Produces a ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0 register field value suitable for setting the register. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0_SET(value) (((value) << 0) & 0x0000007f)

/*
 * Field : uncor_err_b0
 * 
 * Uncorrectable error occurred while reading pages for last transaction in Bank0.
 * Uncorrectable errors also generate interrupts in intr_statusx register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0_MSB        7
/* The width in bits of the ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0_WIDTH      1
/* The mask used to set the ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0_SET_MSK    0x00000080
/* The mask used to clear the ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0_CLR_MSK    0xffffff7f
/* The reset value of the ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0_RESET      0x0
/* Extracts the ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0 field value from a register. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0 register field value suitable for setting the register. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : max_errors_b1
 * 
 * Maximum of number of errors corrected per sector in Bank1. This field is not
 * valid for uncorrectable errors. A value of zero indicates that no ECC error
 * occurred in last completed transaction.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1_MSB        14
/* The width in bits of the ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1_WIDTH      7
/* The mask used to set the ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1_SET_MSK    0x00007f00
/* The mask used to clear the ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1_CLR_MSK    0xffff80ff
/* The reset value of the ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1_RESET      0x0
/* Extracts the ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1 field value from a register. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1_GET(value) (((value) & 0x00007f00) >> 8)
/* Produces a ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1 register field value suitable for setting the register. */
#define ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1_SET(value) (((value) << 8) & 0x00007f00)

/*
 * Field : uncor_err_b1
 * 
 * Uncorrectable error occurred while reading pages for last transaction in Bank1.
 * Uncorrectable errors also generate interrupts in intr_statusx register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1_MSB        15
/* The width in bits of the ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1_WIDTH      1
/* The mask used to set the ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1_SET_MSK    0x00008000
/* The mask used to clear the ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1_CLR_MSK    0xffff7fff
/* The reset value of the ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1_RESET      0x0
/* Extracts the ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1 field value from a register. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1 register field value suitable for setting the register. */
#define ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1_SET(value) (((value) << 15) & 0x00008000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_ECC_ECCCORINFO_B01.
 */
struct ALT_NAND_ECC_ECCCORINFO_B01_s
{
    const uint32_t  max_errors_b0 :  7;  /* ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B0 */
    const uint32_t  uncor_err_b0  :  1;  /* ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B0 */
    const uint32_t  max_errors_b1 :  7;  /* ALT_NAND_ECC_ECCCORINFO_B01_MAX_ERRORS_B1 */
    const uint32_t  uncor_err_b1  :  1;  /* ALT_NAND_ECC_ECCCORINFO_B01_UNCOR_ERR_B1 */
    uint32_t                      : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_ECC_ECCCORINFO_B01. */
typedef volatile struct ALT_NAND_ECC_ECCCORINFO_B01_s  ALT_NAND_ECC_ECCCORINFO_B01_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_ECC_ECCCORINFO_B01 register from the beginning of the component. */
#define ALT_NAND_ECC_ECCCORINFO_B01_OFST        0x0

/*
 * Register : ECCCorInfo_b23
 * 
 * ECC Error correction Information register. Controller updates this register when
 * it completes a transaction. The values are held in this register till a new
 * transaction completes.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                              
 * :--------|:-------|:------|:------------------------------------------
 *  [6:0]   | R      | 0x0   | ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2
 *  [7]     | R      | 0x0   | ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2 
 *  [14:8]  | R      | 0x0   | ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3
 *  [15]    | R      | 0x0   | ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3 
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                              
 * 
 */
/*
 * Field : max_errors_b2
 * 
 * Maximum of number of errors corrected per sector in Bank2. This field is not
 * valid for uncorrectable errors. A value of zero indicates that no ECC error
 * occurred in last completed transaction.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2_MSB        6
/* The width in bits of the ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2_WIDTH      7
/* The mask used to set the ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2_SET_MSK    0x0000007f
/* The mask used to clear the ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2_CLR_MSK    0xffffff80
/* The reset value of the ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2_RESET      0x0
/* Extracts the ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2 field value from a register. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2_GET(value) (((value) & 0x0000007f) >> 0)
/* Produces a ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2 register field value suitable for setting the register. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2_SET(value) (((value) << 0) & 0x0000007f)

/*
 * Field : uncor_err_b2
 * 
 * Uncorrectable error occurred while reading pages for last transaction in Bank2.
 * Uncorrectable errors also generate interrupts in intr_statusx register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2_MSB        7
/* The width in bits of the ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2_WIDTH      1
/* The mask used to set the ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2_SET_MSK    0x00000080
/* The mask used to clear the ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2_CLR_MSK    0xffffff7f
/* The reset value of the ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2_RESET      0x0
/* Extracts the ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2 field value from a register. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2 register field value suitable for setting the register. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : max_errors_b3
 * 
 * Maximum of number of errors corrected per sector in Bank3. This field is not
 * valid for uncorrectable errors. A value of zero indicates that no ECC error
 * occurred in last completed transaction.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3_MSB        14
/* The width in bits of the ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3_WIDTH      7
/* The mask used to set the ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3_SET_MSK    0x00007f00
/* The mask used to clear the ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3_CLR_MSK    0xffff80ff
/* The reset value of the ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3_RESET      0x0
/* Extracts the ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3 field value from a register. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3_GET(value) (((value) & 0x00007f00) >> 8)
/* Produces a ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3 register field value suitable for setting the register. */
#define ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3_SET(value) (((value) << 8) & 0x00007f00)

/*
 * Field : uncor_err_b3
 * 
 * Uncorrectable error occurred while reading pages for last transaction in Bank3.
 * Uncorrectable errors also generate interrupts in intr_statusx register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3_MSB        15
/* The width in bits of the ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3_WIDTH      1
/* The mask used to set the ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3_SET_MSK    0x00008000
/* The mask used to clear the ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3 register field value. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3_CLR_MSK    0xffff7fff
/* The reset value of the ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3 register field. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3_RESET      0x0
/* Extracts the ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3 field value from a register. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3 register field value suitable for setting the register. */
#define ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3_SET(value) (((value) << 15) & 0x00008000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_ECC_ECCCORINFO_B23.
 */
struct ALT_NAND_ECC_ECCCORINFO_B23_s
{
    const uint32_t  max_errors_b2 :  7;  /* ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B2 */
    const uint32_t  uncor_err_b2  :  1;  /* ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B2 */
    const uint32_t  max_errors_b3 :  7;  /* ALT_NAND_ECC_ECCCORINFO_B23_MAX_ERRORS_B3 */
    const uint32_t  uncor_err_b3  :  1;  /* ALT_NAND_ECC_ECCCORINFO_B23_UNCOR_ERR_B3 */
    uint32_t                      : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_ECC_ECCCORINFO_B23. */
typedef volatile struct ALT_NAND_ECC_ECCCORINFO_B23_s  ALT_NAND_ECC_ECCCORINFO_B23_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_ECC_ECCCORINFO_B23 register from the beginning of the component. */
#define ALT_NAND_ECC_ECCCORINFO_B23_OFST        0x10

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_NAND_ECC.
 */
struct ALT_NAND_ECC_s
{
    volatile ALT_NAND_ECC_ECCCORINFO_B01_t  ECCCorInfo_b01;   /* ALT_NAND_ECC_ECCCORINFO_B01 */
    volatile uint32_t                       _pad_0x4_0xf[3];  /* *UNDEFINED* */
    volatile ALT_NAND_ECC_ECCCORINFO_B23_t  ECCCorInfo_b23;   /* ALT_NAND_ECC_ECCCORINFO_B23 */
};

/* The typedef declaration for register group ALT_NAND_ECC. */
typedef volatile struct ALT_NAND_ECC_s  ALT_NAND_ECC_t;
/* The struct declaration for the raw register contents of register group ALT_NAND_ECC. */
struct ALT_NAND_ECC_raw_s
{
    volatile uint32_t  ECCCorInfo_b01;   /* ALT_NAND_ECC_ECCCORINFO_B01 */
    volatile uint32_t  _pad_0x4_0xf[3];  /* *UNDEFINED* */
    volatile uint32_t  ECCCorInfo_b23;   /* ALT_NAND_ECC_ECCCORINFO_B23 */
};

/* The typedef declaration for the raw register contents of register group ALT_NAND_ECC. */
typedef volatile struct ALT_NAND_ECC_raw_s  ALT_NAND_ECC_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : DMA registers - ALT_NAND_DMA
 * DMA registers
 * 
 * 
 */
/*
 * Register : dma_enable
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description             
 * :-------|:-------|:------|:-------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_DMA_DMA_EN_FLAG
 *  [31:1] | ???    | 0x0   | *UNDEFINED*             
 * 
 */
/*
 * Field : flag
 * 
 * Enables data DMA operation in the controller 1 - Enable DMA 0 - Disable DMA
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_DMA_DMA_EN_FLAG register field. */
#define ALT_NAND_DMA_DMA_EN_FLAG_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_DMA_DMA_EN_FLAG register field. */
#define ALT_NAND_DMA_DMA_EN_FLAG_MSB        0
/* The width in bits of the ALT_NAND_DMA_DMA_EN_FLAG register field. */
#define ALT_NAND_DMA_DMA_EN_FLAG_WIDTH      1
/* The mask used to set the ALT_NAND_DMA_DMA_EN_FLAG register field value. */
#define ALT_NAND_DMA_DMA_EN_FLAG_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_DMA_DMA_EN_FLAG register field value. */
#define ALT_NAND_DMA_DMA_EN_FLAG_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_DMA_DMA_EN_FLAG register field. */
#define ALT_NAND_DMA_DMA_EN_FLAG_RESET      0x0
/* Extracts the ALT_NAND_DMA_DMA_EN_FLAG field value from a register. */
#define ALT_NAND_DMA_DMA_EN_FLAG_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_DMA_DMA_EN_FLAG register field value suitable for setting the register. */
#define ALT_NAND_DMA_DMA_EN_FLAG_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_DMA_DMA_EN.
 */
struct ALT_NAND_DMA_DMA_EN_s
{
    uint32_t  flag :  1;  /* ALT_NAND_DMA_DMA_EN_FLAG */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_DMA_DMA_EN. */
typedef volatile struct ALT_NAND_DMA_DMA_EN_s  ALT_NAND_DMA_DMA_EN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_DMA_DMA_EN register from the beginning of the component. */
#define ALT_NAND_DMA_DMA_EN_OFST        0x0

/*
 * Register : dma_intr
 * 
 * DMA interrupt register
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                    
 * :-------|:-------|:------|:--------------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_DMA_DMA_INTR_TGT_ERROR
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                    
 * 
 */
/*
 * Field : target_error
 * 
 * Controller initiator interface received an ERROR target response for a
 * transaction.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_DMA_DMA_INTR_TGT_ERROR register field. */
#define ALT_NAND_DMA_DMA_INTR_TGT_ERROR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_DMA_DMA_INTR_TGT_ERROR register field. */
#define ALT_NAND_DMA_DMA_INTR_TGT_ERROR_MSB        0
/* The width in bits of the ALT_NAND_DMA_DMA_INTR_TGT_ERROR register field. */
#define ALT_NAND_DMA_DMA_INTR_TGT_ERROR_WIDTH      1
/* The mask used to set the ALT_NAND_DMA_DMA_INTR_TGT_ERROR register field value. */
#define ALT_NAND_DMA_DMA_INTR_TGT_ERROR_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_DMA_DMA_INTR_TGT_ERROR register field value. */
#define ALT_NAND_DMA_DMA_INTR_TGT_ERROR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_DMA_DMA_INTR_TGT_ERROR register field. */
#define ALT_NAND_DMA_DMA_INTR_TGT_ERROR_RESET      0x0
/* Extracts the ALT_NAND_DMA_DMA_INTR_TGT_ERROR field value from a register. */
#define ALT_NAND_DMA_DMA_INTR_TGT_ERROR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_DMA_DMA_INTR_TGT_ERROR register field value suitable for setting the register. */
#define ALT_NAND_DMA_DMA_INTR_TGT_ERROR_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_DMA_DMA_INTR.
 */
struct ALT_NAND_DMA_DMA_INTR_s
{
    uint32_t  target_error :  1;  /* ALT_NAND_DMA_DMA_INTR_TGT_ERROR */
    uint32_t               : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_DMA_DMA_INTR. */
typedef volatile struct ALT_NAND_DMA_DMA_INTR_s  ALT_NAND_DMA_DMA_INTR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_DMA_DMA_INTR register from the beginning of the component. */
#define ALT_NAND_DMA_DMA_INTR_OFST        0x20

/*
 * Register : dma_intr_en
 * 
 * Enables corresponding interrupt bit in dma interrupt register
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                       
 * :-------|:-------|:------|:-----------------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                       
 * 
 */
/*
 * Field : target_error
 * 
 * Controller initiator interface received an ERROR target response for a
 * transaction.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR register field. */
#define ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR register field. */
#define ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR_MSB        0
/* The width in bits of the ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR register field. */
#define ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR_WIDTH      1
/* The mask used to set the ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR register field value. */
#define ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR register field value. */
#define ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR register field. */
#define ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR_RESET      0x0
/* Extracts the ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR field value from a register. */
#define ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR register field value suitable for setting the register. */
#define ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_DMA_DMA_INTR_EN.
 */
struct ALT_NAND_DMA_DMA_INTR_EN_s
{
    uint32_t  target_error :  1;  /* ALT_NAND_DMA_DMA_INTR_EN_TGT_ERROR */
    uint32_t               : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_DMA_DMA_INTR_EN. */
typedef volatile struct ALT_NAND_DMA_DMA_INTR_EN_s  ALT_NAND_DMA_DMA_INTR_EN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_DMA_DMA_INTR_EN register from the beginning of the component. */
#define ALT_NAND_DMA_DMA_INTR_EN_OFST        0x30

/*
 * Register : target_err_addr_lo
 * 
 * Transaction address for which controller initiator interface received an ERROR
 * target response.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                       
 * :--------|:-------|:------|:-----------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                       
 * 
 */
/*
 * Field : value
 * 
 * Least significant 16 bits
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE register field. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE register field. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE_MSB        15
/* The width in bits of the ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE register field. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE register field value. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE register field value. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE register field. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE_RESET      0x0
/* Extracts the ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE field value from a register. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE register field value suitable for setting the register. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_DMA_TGT_ERR_ADDR_LO.
 */
struct ALT_NAND_DMA_TGT_ERR_ADDR_LO_s
{
    const uint32_t  value : 16;  /* ALT_NAND_DMA_TGT_ERR_ADDR_LO_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_DMA_TGT_ERR_ADDR_LO. */
typedef volatile struct ALT_NAND_DMA_TGT_ERR_ADDR_LO_s  ALT_NAND_DMA_TGT_ERR_ADDR_LO_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_DMA_TGT_ERR_ADDR_LO register from the beginning of the component. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_LO_OFST        0x40

/*
 * Register : target_err_addr_hi
 * 
 * Transaction address for which controller initiator interface received an ERROR
 * target response.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                       
 * :--------|:-------|:------|:-----------------------------------
 *  [15:0]  | R      | 0x0   | ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                       
 * 
 */
/*
 * Field : value
 * 
 * Most significant 16 bits
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE register field. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE register field. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE_MSB        15
/* The width in bits of the ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE register field. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE register field value. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE register field value. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE register field. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE_RESET      0x0
/* Extracts the ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE field value from a register. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE register field value suitable for setting the register. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_DMA_TGT_ERR_ADDR_HI.
 */
struct ALT_NAND_DMA_TGT_ERR_ADDR_HI_s
{
    const uint32_t  value : 16;  /* ALT_NAND_DMA_TGT_ERR_ADDR_HI_VALUE */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_DMA_TGT_ERR_ADDR_HI. */
typedef volatile struct ALT_NAND_DMA_TGT_ERR_ADDR_HI_s  ALT_NAND_DMA_TGT_ERR_ADDR_HI_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_DMA_TGT_ERR_ADDR_HI register from the beginning of the component. */
#define ALT_NAND_DMA_TGT_ERR_ADDR_HI_OFST        0x50

/*
 * Register : flash_burst_length
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                                
 * :-------|:-------|:------|:--------------------------------------------
 *  [1:0]  | RW     | 0x1   | ALT_NAND_DMA_FLSH_BURST_LEN_VALUE          
 *  [3:2]  | ???    | 0x0   | *UNDEFINED*                                
 *  [4]    | RW     | 0x0   | ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST
 *  [7:5]  | ???    | 0x0   | *UNDEFINED*                                
 *  [31:8] | RW     | 0x0   | ALT_NAND_DMA_FLSH_BURST_LEN_RSVD           
 * 
 */
/*
 * Field : value
 * 
 * Sets the burst used by data dma for transferring data to/from flash device. This
 * burst length is different and is larger than the burst length on the host bus so
 * that larger amount of data can be transferred to/from device, descreasing
 * controller data transfer overhead in the process. 00 - 64 bytes, 01 - 128 bytes,
 * 10 - 256 bytes, 11 - 512 bytes. The host burst size multiplied by the number of
 * outstanding requests on the host side should be greater than equal to this
 * value. If not, the device side burst length will be equal to host side burst
 * length.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_DMA_FLSH_BURST_LEN_VALUE register field. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_DMA_FLSH_BURST_LEN_VALUE register field. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_VALUE_MSB        1
/* The width in bits of the ALT_NAND_DMA_FLSH_BURST_LEN_VALUE register field. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_VALUE_WIDTH      2
/* The mask used to set the ALT_NAND_DMA_FLSH_BURST_LEN_VALUE register field value. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_VALUE_SET_MSK    0x00000003
/* The mask used to clear the ALT_NAND_DMA_FLSH_BURST_LEN_VALUE register field value. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_VALUE_CLR_MSK    0xfffffffc
/* The reset value of the ALT_NAND_DMA_FLSH_BURST_LEN_VALUE register field. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_VALUE_RESET      0x1
/* Extracts the ALT_NAND_DMA_FLSH_BURST_LEN_VALUE field value from a register. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_VALUE_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_NAND_DMA_FLSH_BURST_LEN_VALUE register field value suitable for setting the register. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_VALUE_SET(value) (((value) << 0) & 0x00000003)

/*
 * Field : continous_burst
 * 
 * When this bit is set, the Data DMA will burst the entire page from/to the flash
 * device. Please make sure that the host system can provide/sink data at a fast
 * pace to avoid unnecessary pausing of data on the device interface.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST register field. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST register field. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST_MSB        4
/* The width in bits of the ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST register field. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST_WIDTH      1
/* The mask used to set the ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST register field value. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST_SET_MSK    0x00000010
/* The mask used to clear the ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST register field value. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST_CLR_MSK    0xffffffef
/* The reset value of the ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST register field. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST_RESET      0x0
/* Extracts the ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST field value from a register. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST register field value suitable for setting the register. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : reserved
 * 
 * Reserved
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_DMA_FLSH_BURST_LEN_RSVD register field. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_RSVD_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_NAND_DMA_FLSH_BURST_LEN_RSVD register field. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_RSVD_MSB        31
/* The width in bits of the ALT_NAND_DMA_FLSH_BURST_LEN_RSVD register field. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_RSVD_WIDTH      24
/* The mask used to set the ALT_NAND_DMA_FLSH_BURST_LEN_RSVD register field value. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_RSVD_SET_MSK    0xffffff00
/* The mask used to clear the ALT_NAND_DMA_FLSH_BURST_LEN_RSVD register field value. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_RSVD_CLR_MSK    0x000000ff
/* The reset value of the ALT_NAND_DMA_FLSH_BURST_LEN_RSVD register field. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_RSVD_RESET      0x0
/* Extracts the ALT_NAND_DMA_FLSH_BURST_LEN_RSVD field value from a register. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_RSVD_GET(value) (((value) & 0xffffff00) >> 8)
/* Produces a ALT_NAND_DMA_FLSH_BURST_LEN_RSVD register field value suitable for setting the register. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_RSVD_SET(value) (((value) << 8) & 0xffffff00)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_DMA_FLSH_BURST_LEN.
 */
struct ALT_NAND_DMA_FLSH_BURST_LEN_s
{
    uint32_t  value           :  2;  /* ALT_NAND_DMA_FLSH_BURST_LEN_VALUE */
    uint32_t                  :  2;  /* *UNDEFINED* */
    uint32_t  continous_burst :  1;  /* ALT_NAND_DMA_FLSH_BURST_LEN_CONTINOUS_BURST */
    uint32_t                  :  3;  /* *UNDEFINED* */
    uint32_t  reserved        : 24;  /* ALT_NAND_DMA_FLSH_BURST_LEN_RSVD */
};

/* The typedef declaration for register ALT_NAND_DMA_FLSH_BURST_LEN. */
typedef volatile struct ALT_NAND_DMA_FLSH_BURST_LEN_s  ALT_NAND_DMA_FLSH_BURST_LEN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_DMA_FLSH_BURST_LEN register from the beginning of the component. */
#define ALT_NAND_DMA_FLSH_BURST_LEN_OFST        0x70

/*
 * Register : chip_interleave_enable_and_allow_int_reads
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                                  
 * :-------|:-------|:------|:----------------------------------------------
 *  [0]    | RW     | 0x0   | ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN           
 *  [3:1]  | ???    | 0x0   | *UNDEFINED*                                  
 *  [4]    | RW     | 0x1   | ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS
 *  [31:5] | ???    | 0x0   | *UNDEFINED*                                  
 * 
 */
/*
 * Field : chip_interleave_enable
 * 
 * This bit informs the controller to enable or disable interleaving among
 * banks/LUNS to increase the net performance of the controller. [list][*]1 -
 * Enable interleaving [*]0 - Disable Interleaving[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN register field. */
#define ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN register field. */
#define ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN_MSB        0
/* The width in bits of the ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN register field. */
#define ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN_WIDTH      1
/* The mask used to set the ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN register field value. */
#define ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN_SET_MSK    0x00000001
/* The mask used to clear the ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN register field value. */
#define ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN register field. */
#define ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN_RESET      0x0
/* Extracts the ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN field value from a register. */
#define ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN register field value suitable for setting the register. */
#define ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : allow_int_reads_within_luns
 * 
 * This bit informs the controller to enable or disable simultaneous read accesses
 * to different LUNS in the same bank. This bit is of importance only if the
 * controller supports interleaved operations among LUNs and if the device has
 * multiple LUNS. If the bit is disabled, the controller will send read commands to
 * different LUNS of of the same bank only sequentially and if enabled, the
 * controller will issue simultaneous read accesses to LUNS of same bank if
 * required. [list][*]1 - Enable [*]0 - Disable[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS register field. */
#define ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS register field. */
#define ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS_MSB        4
/* The width in bits of the ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS register field. */
#define ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS_WIDTH      1
/* The mask used to set the ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS register field value. */
#define ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS_SET_MSK    0x00000010
/* The mask used to clear the ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS register field value. */
#define ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS_CLR_MSK    0xffffffef
/* The reset value of the ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS register field. */
#define ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS_RESET      0x1
/* Extracts the ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS field value from a register. */
#define ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS register field value suitable for setting the register. */
#define ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS_SET(value) (((value) << 4) & 0x00000010)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_DMA_INTRLV.
 */
struct ALT_NAND_DMA_INTRLV_s
{
    uint32_t  chip_interleave_enable      :  1;  /* ALT_NAND_DMA_INTRLV_CHIP_INTRLV_EN */
    uint32_t                              :  3;  /* *UNDEFINED* */
    uint32_t  allow_int_reads_within_luns :  1;  /* ALT_NAND_DMA_INTRLV_ALLOW_INT_RDS_WITHIN_LUNS */
    uint32_t                              : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_DMA_INTRLV. */
typedef volatile struct ALT_NAND_DMA_INTRLV_s  ALT_NAND_DMA_INTRLV_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_DMA_INTRLV register from the beginning of the component. */
#define ALT_NAND_DMA_INTRLV_OFST        0x80

/*
 * Register : no_of_blocks_per_lun
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                            
 * :-------|:-------|:------|:----------------------------------------
 *  [3:0]  | RW     | 0xf   | ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE
 *  [31:4] | ???    | 0x0   | *UNDEFINED*                            
 * 
 */
/*
 * Field : value
 * 
 * Indicates the first block of next LUN. This information is used for extracting
 * the target LUN during LUN interleaving. After Initialization, if the controller
 * detects an ONFi device, this field is automatically updated by the controller.
 * For other devices, software will need to write to this register for proper
 * interleaving. The value in this register is interpreted as follows- [list][*]0 -
 * Next LUN starts from 1024. [*]1 - Next LUN starts from 2048. [*]2 - Next LUN
 * starts from 4096 and so on... [/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE register field. */
#define ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE register field. */
#define ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE_MSB        3
/* The width in bits of the ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE register field. */
#define ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE_WIDTH      4
/* The mask used to set the ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE register field value. */
#define ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE_SET_MSK    0x0000000f
/* The mask used to clear the ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE register field value. */
#define ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE_CLR_MSK    0xfffffff0
/* The reset value of the ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE register field. */
#define ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE_RESET      0xf
/* Extracts the ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE field value from a register. */
#define ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE register field value suitable for setting the register. */
#define ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE_SET(value) (((value) << 0) & 0x0000000f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN.
 */
struct ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_s
{
    uint32_t  value :  4;  /* ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_VALUE */
    uint32_t        : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN. */
typedef volatile struct ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_s  ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN register from the beginning of the component. */
#define ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_OFST        0x90

/*
 * Register : lun_status_cmd
 * 
 * Indicates the command to be sent while checking status of the next LUN.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset  | Description                    
 * :--------|:-------|:-------|:--------------------------------
 *  [15:0]  | RW     | 0x7878 | ALT_NAND_DMA_LUN_STAT_CMD_VALUE
 *  [31:16] | ???    | 0x0    | *UNDEFINED*                    
 * 
 */
/*
 * Field : value
 * 
 * [list][*]7:0 - Indicates the command to check the status of the first LUN/Die.
 * [*]15:8 - Indicates the command to check the status of the other LUN/Die.[/list]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_NAND_DMA_LUN_STAT_CMD_VALUE register field. */
#define ALT_NAND_DMA_LUN_STAT_CMD_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_NAND_DMA_LUN_STAT_CMD_VALUE register field. */
#define ALT_NAND_DMA_LUN_STAT_CMD_VALUE_MSB        15
/* The width in bits of the ALT_NAND_DMA_LUN_STAT_CMD_VALUE register field. */
#define ALT_NAND_DMA_LUN_STAT_CMD_VALUE_WIDTH      16
/* The mask used to set the ALT_NAND_DMA_LUN_STAT_CMD_VALUE register field value. */
#define ALT_NAND_DMA_LUN_STAT_CMD_VALUE_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_NAND_DMA_LUN_STAT_CMD_VALUE register field value. */
#define ALT_NAND_DMA_LUN_STAT_CMD_VALUE_CLR_MSK    0xffff0000
/* The reset value of the ALT_NAND_DMA_LUN_STAT_CMD_VALUE register field. */
#define ALT_NAND_DMA_LUN_STAT_CMD_VALUE_RESET      0x7878
/* Extracts the ALT_NAND_DMA_LUN_STAT_CMD_VALUE field value from a register. */
#define ALT_NAND_DMA_LUN_STAT_CMD_VALUE_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_NAND_DMA_LUN_STAT_CMD_VALUE register field value suitable for setting the register. */
#define ALT_NAND_DMA_LUN_STAT_CMD_VALUE_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_NAND_DMA_LUN_STAT_CMD.
 */
struct ALT_NAND_DMA_LUN_STAT_CMD_s
{
    uint32_t  value : 16;  /* ALT_NAND_DMA_LUN_STAT_CMD_VALUE */
    uint32_t        : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_NAND_DMA_LUN_STAT_CMD. */
typedef volatile struct ALT_NAND_DMA_LUN_STAT_CMD_s  ALT_NAND_DMA_LUN_STAT_CMD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_NAND_DMA_LUN_STAT_CMD register from the beginning of the component. */
#define ALT_NAND_DMA_LUN_STAT_CMD_OFST        0xa0

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_NAND_DMA.
 */
struct ALT_NAND_DMA_s
{
    volatile ALT_NAND_DMA_DMA_EN_t                dma_enable;                                  /* ALT_NAND_DMA_DMA_EN */
    volatile uint32_t                             _pad_0x4_0x1f[7];                            /* *UNDEFINED* */
    volatile ALT_NAND_DMA_DMA_INTR_t              dma_intr;                                    /* ALT_NAND_DMA_DMA_INTR */
    volatile uint32_t                             _pad_0x24_0x2f[3];                           /* *UNDEFINED* */
    volatile ALT_NAND_DMA_DMA_INTR_EN_t           dma_intr_en;                                 /* ALT_NAND_DMA_DMA_INTR_EN */
    volatile uint32_t                             _pad_0x34_0x3f[3];                           /* *UNDEFINED* */
    volatile ALT_NAND_DMA_TGT_ERR_ADDR_LO_t       target_err_addr_lo;                          /* ALT_NAND_DMA_TGT_ERR_ADDR_LO */
    volatile uint32_t                             _pad_0x44_0x4f[3];                           /* *UNDEFINED* */
    volatile ALT_NAND_DMA_TGT_ERR_ADDR_HI_t       target_err_addr_hi;                          /* ALT_NAND_DMA_TGT_ERR_ADDR_HI */
    volatile uint32_t                             _pad_0x54_0x6f[7];                           /* *UNDEFINED* */
    volatile ALT_NAND_DMA_FLSH_BURST_LEN_t        flash_burst_length;                          /* ALT_NAND_DMA_FLSH_BURST_LEN */
    volatile uint32_t                             _pad_0x74_0x7f[3];                           /* *UNDEFINED* */
    volatile ALT_NAND_DMA_INTRLV_t                chip_interleave_enable_and_allow_int_reads;  /* ALT_NAND_DMA_INTRLV */
    volatile uint32_t                             _pad_0x84_0x8f[3];                           /* *UNDEFINED* */
    volatile ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN_t  no_of_blocks_per_lun;                        /* ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN */
    volatile uint32_t                             _pad_0x94_0x9f[3];                           /* *UNDEFINED* */
    volatile ALT_NAND_DMA_LUN_STAT_CMD_t          lun_status_cmd;                              /* ALT_NAND_DMA_LUN_STAT_CMD */
};

/* The typedef declaration for register group ALT_NAND_DMA. */
typedef volatile struct ALT_NAND_DMA_s  ALT_NAND_DMA_t;
/* The struct declaration for the raw register contents of register group ALT_NAND_DMA. */
struct ALT_NAND_DMA_raw_s
{
    volatile uint32_t  dma_enable;                                  /* ALT_NAND_DMA_DMA_EN */
    volatile uint32_t  _pad_0x4_0x1f[7];                            /* *UNDEFINED* */
    volatile uint32_t  dma_intr;                                    /* ALT_NAND_DMA_DMA_INTR */
    volatile uint32_t  _pad_0x24_0x2f[3];                           /* *UNDEFINED* */
    volatile uint32_t  dma_intr_en;                                 /* ALT_NAND_DMA_DMA_INTR_EN */
    volatile uint32_t  _pad_0x34_0x3f[3];                           /* *UNDEFINED* */
    volatile uint32_t  target_err_addr_lo;                          /* ALT_NAND_DMA_TGT_ERR_ADDR_LO */
    volatile uint32_t  _pad_0x44_0x4f[3];                           /* *UNDEFINED* */
    volatile uint32_t  target_err_addr_hi;                          /* ALT_NAND_DMA_TGT_ERR_ADDR_HI */
    volatile uint32_t  _pad_0x54_0x6f[7];                           /* *UNDEFINED* */
    volatile uint32_t  flash_burst_length;                          /* ALT_NAND_DMA_FLSH_BURST_LEN */
    volatile uint32_t  _pad_0x74_0x7f[3];                           /* *UNDEFINED* */
    volatile uint32_t  chip_interleave_enable_and_allow_int_reads;  /* ALT_NAND_DMA_INTRLV */
    volatile uint32_t  _pad_0x84_0x8f[3];                           /* *UNDEFINED* */
    volatile uint32_t  no_of_blocks_per_lun;                        /* ALT_NAND_DMA_NO_OF_BLOCKS_PER_LUN */
    volatile uint32_t  _pad_0x94_0x9f[3];                           /* *UNDEFINED* */
    volatile uint32_t  lun_status_cmd;                              /* ALT_NAND_DMA_LUN_STAT_CMD */
};

/* The typedef declaration for the raw register contents of register group ALT_NAND_DMA. */
typedef volatile struct ALT_NAND_DMA_raw_s  ALT_NAND_DMA_raw_t;
#endif  /* __ASSEMBLY__ */


#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_NAND.
 */
struct ALT_NAND_s
{
    volatile ALT_NAND_CFG_t    config;                /* ALT_NAND_CFG */
    volatile uint32_t          _pad_0x2b4_0x2ff[19];  /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_t  param;                 /* ALT_NAND_PARAM */
    volatile uint32_t          _pad_0x3f4_0x3ff[3];   /* *UNDEFINED* */
    volatile ALT_NAND_STAT_t   status;                /* ALT_NAND_STAT */
    volatile uint32_t          _pad_0x544_0x64f[67];  /* *UNDEFINED* */
    volatile ALT_NAND_ECC_t    ecc;                   /* ALT_NAND_ECC */
    volatile uint32_t          _pad_0x664_0x6ff[39];  /* *UNDEFINED* */
    volatile ALT_NAND_DMA_t    dma;                   /* ALT_NAND_DMA */
    volatile uint32_t          _pad_0x7a4_0x800[23];  /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_NAND. */
typedef volatile struct ALT_NAND_s  ALT_NAND_t;
/* The struct declaration for the raw register contents of register group ALT_NAND. */
struct ALT_NAND_raw_s
{
    volatile ALT_NAND_CFG_raw_t    config;                /* ALT_NAND_CFG */
    volatile uint32_t              _pad_0x2b4_0x2ff[19];  /* *UNDEFINED* */
    volatile ALT_NAND_PARAM_raw_t  param;                 /* ALT_NAND_PARAM */
    volatile uint32_t              _pad_0x3f4_0x3ff[3];   /* *UNDEFINED* */
    volatile ALT_NAND_STAT_raw_t   status;                /* ALT_NAND_STAT */
    volatile uint32_t              _pad_0x544_0x64f[67];  /* *UNDEFINED* */
    volatile ALT_NAND_ECC_raw_t    ecc;                   /* ALT_NAND_ECC */
    volatile uint32_t              _pad_0x664_0x6ff[39];  /* *UNDEFINED* */
    volatile ALT_NAND_DMA_raw_t    dma;                   /* ALT_NAND_DMA */
    volatile uint32_t              _pad_0x7a4_0x800[23];  /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_NAND. */
typedef volatile struct ALT_NAND_raw_s  ALT_NAND_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_NAND_H__ */

