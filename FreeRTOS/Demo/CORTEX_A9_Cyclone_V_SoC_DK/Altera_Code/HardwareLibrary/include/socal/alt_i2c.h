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

/* Altera - ALT_I2C */

#ifndef __ALTERA_ALT_I2C_H__
#define __ALTERA_ALT_I2C_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : I2C Module - ALT_I2C
 * I2C Module
 * 
 * Registers in the I2C module
 * 
 */
/*
 * Register : Control Register - ic_con
 * 
 * This register can be written only when the I2C is disabled, which corresponds to
 * the Bit [0] of the Enable Register being set to 0. Writes at other times have no
 * effect.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description         
 * :-------|:-------|:------|:---------------------
 *  [0]    | RW     | 0x1   | Master Enable       
 *  [2:1]  | RW     | 0x2   | Master Speed Control
 *  [3]    | RW     | 0x1   | Slave Address Size  
 *  [4]    | RW     | 0x1   | Master Address Size 
 *  [5]    | RW     | 0x1   | Restart Enable      
 *  [6]    | RW     | 0x1   | Slave Disable       
 *  [31:7] | ???    | 0x0   | *UNDEFINED*         
 * 
 */
/*
 * Field : Master Enable - master_mode
 * 
 * This bit controls whether the i2c master is enabled.
 * 
 * NOTE: Software should ensure that if this bit is written with '1', then bit 6
 * should also be written with a '1'.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description    
 * :--------------------------|:------|:----------------
 *  ALT_I2C_CON_MST_MOD_E_DIS | 0x0   | master disabled
 *  ALT_I2C_CON_MST_MOD_E_EN  | 0x1   | master enabled 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_CON_MST_MOD
 * 
 * master disabled
 */
#define ALT_I2C_CON_MST_MOD_E_DIS   0x0
/*
 * Enumerated value for register field ALT_I2C_CON_MST_MOD
 * 
 * master enabled
 */
#define ALT_I2C_CON_MST_MOD_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_CON_MST_MOD register field. */
#define ALT_I2C_CON_MST_MOD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_CON_MST_MOD register field. */
#define ALT_I2C_CON_MST_MOD_MSB        0
/* The width in bits of the ALT_I2C_CON_MST_MOD register field. */
#define ALT_I2C_CON_MST_MOD_WIDTH      1
/* The mask used to set the ALT_I2C_CON_MST_MOD register field value. */
#define ALT_I2C_CON_MST_MOD_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_CON_MST_MOD register field value. */
#define ALT_I2C_CON_MST_MOD_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_CON_MST_MOD register field. */
#define ALT_I2C_CON_MST_MOD_RESET      0x1
/* Extracts the ALT_I2C_CON_MST_MOD field value from a register. */
#define ALT_I2C_CON_MST_MOD_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_CON_MST_MOD register field value suitable for setting the register. */
#define ALT_I2C_CON_MST_MOD_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Master Speed Control - speed
 * 
 * These bits control at which speed the I2C operates, its setting is relevant only
 * if one is operating the I2C in master mode. Hardware protects against illegal
 * values being programmed by software. This field should be programmed only with
 * standard or fast speed.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description               
 * :-----------------------------|:------|:---------------------------
 *  ALT_I2C_CON_SPEED_E_STANDARD | 0x1   | standard mode (100 kbit/s)
 *  ALT_I2C_CON_SPEED_E_FAST     | 0x2   | fast mode (400 kbit/s)    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_CON_SPEED
 * 
 * standard mode (100 kbit/s)
 */
#define ALT_I2C_CON_SPEED_E_STANDARD    0x1
/*
 * Enumerated value for register field ALT_I2C_CON_SPEED
 * 
 * fast mode (400 kbit/s)
 */
#define ALT_I2C_CON_SPEED_E_FAST        0x2

/* The Least Significant Bit (LSB) position of the ALT_I2C_CON_SPEED register field. */
#define ALT_I2C_CON_SPEED_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_I2C_CON_SPEED register field. */
#define ALT_I2C_CON_SPEED_MSB        2
/* The width in bits of the ALT_I2C_CON_SPEED register field. */
#define ALT_I2C_CON_SPEED_WIDTH      2
/* The mask used to set the ALT_I2C_CON_SPEED register field value. */
#define ALT_I2C_CON_SPEED_SET_MSK    0x00000006
/* The mask used to clear the ALT_I2C_CON_SPEED register field value. */
#define ALT_I2C_CON_SPEED_CLR_MSK    0xfffffff9
/* The reset value of the ALT_I2C_CON_SPEED register field. */
#define ALT_I2C_CON_SPEED_RESET      0x2
/* Extracts the ALT_I2C_CON_SPEED field value from a register. */
#define ALT_I2C_CON_SPEED_GET(value) (((value) & 0x00000006) >> 1)
/* Produces a ALT_I2C_CON_SPEED register field value suitable for setting the register. */
#define ALT_I2C_CON_SPEED_SET(value) (((value) << 1) & 0x00000006)

/*
 * Field : Slave Address Size - ic_10bitaddr_slave
 * 
 * When acting as a slave, this bit controls whether the I2C responds to 7- or
 * 10-bit addresses. In 7-bit addressing, only the lower 7 bits of  the Slave
 * Address Register are compared. The I2C responds will only respond to 10-bit
 * addressing transfers that match the full 10 bits of the Slave Address register.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                        | Value | Description      
 * :--------------------------------------------|:------|:------------------
 *  ALT_I2C_CON_IC_10BITADDR_SLV_E_SLVADDR7BIT  | 0x0   | 7-bit addressing 
 *  ALT_I2C_CON_IC_10BITADDR_SLV_E_SLVADDR10BIT | 0x1   | 10-bit addressing
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_CON_IC_10BITADDR_SLV
 * 
 * 7-bit addressing
 */
#define ALT_I2C_CON_IC_10BITADDR_SLV_E_SLVADDR7BIT  0x0
/*
 * Enumerated value for register field ALT_I2C_CON_IC_10BITADDR_SLV
 * 
 * 10-bit addressing
 */
#define ALT_I2C_CON_IC_10BITADDR_SLV_E_SLVADDR10BIT 0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_CON_IC_10BITADDR_SLV register field. */
#define ALT_I2C_CON_IC_10BITADDR_SLV_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_I2C_CON_IC_10BITADDR_SLV register field. */
#define ALT_I2C_CON_IC_10BITADDR_SLV_MSB        3
/* The width in bits of the ALT_I2C_CON_IC_10BITADDR_SLV register field. */
#define ALT_I2C_CON_IC_10BITADDR_SLV_WIDTH      1
/* The mask used to set the ALT_I2C_CON_IC_10BITADDR_SLV register field value. */
#define ALT_I2C_CON_IC_10BITADDR_SLV_SET_MSK    0x00000008
/* The mask used to clear the ALT_I2C_CON_IC_10BITADDR_SLV register field value. */
#define ALT_I2C_CON_IC_10BITADDR_SLV_CLR_MSK    0xfffffff7
/* The reset value of the ALT_I2C_CON_IC_10BITADDR_SLV register field. */
#define ALT_I2C_CON_IC_10BITADDR_SLV_RESET      0x1
/* Extracts the ALT_I2C_CON_IC_10BITADDR_SLV field value from a register. */
#define ALT_I2C_CON_IC_10BITADDR_SLV_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_I2C_CON_IC_10BITADDR_SLV register field value suitable for setting the register. */
#define ALT_I2C_CON_IC_10BITADDR_SLV_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Master Address Size - ic_10bitaddr_master
 * 
 * This bit controls whether the I2C starts its transfers in 7-or 10-bit addressing
 * mode when acting as a master.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                        | Value | Description      
 * :--------------------------------------------|:------|:------------------
 *  ALT_I2C_CON_IC_10BITADDR_MST_E_MSTADDR7BIT  | 0x0   | 7-bit addressing 
 *  ALT_I2C_CON_IC_10BITADDR_MST_E_MSTADDR10BIT | 0x1   | 10-bit addressing
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_CON_IC_10BITADDR_MST
 * 
 * 7-bit addressing
 */
#define ALT_I2C_CON_IC_10BITADDR_MST_E_MSTADDR7BIT  0x0
/*
 * Enumerated value for register field ALT_I2C_CON_IC_10BITADDR_MST
 * 
 * 10-bit addressing
 */
#define ALT_I2C_CON_IC_10BITADDR_MST_E_MSTADDR10BIT 0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_CON_IC_10BITADDR_MST register field. */
#define ALT_I2C_CON_IC_10BITADDR_MST_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_I2C_CON_IC_10BITADDR_MST register field. */
#define ALT_I2C_CON_IC_10BITADDR_MST_MSB        4
/* The width in bits of the ALT_I2C_CON_IC_10BITADDR_MST register field. */
#define ALT_I2C_CON_IC_10BITADDR_MST_WIDTH      1
/* The mask used to set the ALT_I2C_CON_IC_10BITADDR_MST register field value. */
#define ALT_I2C_CON_IC_10BITADDR_MST_SET_MSK    0x00000010
/* The mask used to clear the ALT_I2C_CON_IC_10BITADDR_MST register field value. */
#define ALT_I2C_CON_IC_10BITADDR_MST_CLR_MSK    0xffffffef
/* The reset value of the ALT_I2C_CON_IC_10BITADDR_MST register field. */
#define ALT_I2C_CON_IC_10BITADDR_MST_RESET      0x1
/* Extracts the ALT_I2C_CON_IC_10BITADDR_MST field value from a register. */
#define ALT_I2C_CON_IC_10BITADDR_MST_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_I2C_CON_IC_10BITADDR_MST register field value suitable for setting the register. */
#define ALT_I2C_CON_IC_10BITADDR_MST_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Restart Enable - ic_restart_en
 * 
 * Determines whether RESTART conditions may be sent when acting as a master. Some
 * older slaves do not support handling RESTART conditions; however, RESTART
 * conditions are used in several I2C operations. When RESTART is disabled, the
 * master is prohibited from performing the following functions
 * 
 * * Changing direction within a transfer (split),
 * 
 * * Sending a START BYTE,
 * 
 * * High-speed mode operation,
 * 
 * * Combined format transfers in 7-bit addressing modes,
 * 
 * * Read operation with a 10-bit address,
 * 
 * * Sending multiple bytes per transfer,
 * 
 * By replacing RESTART condition followed by a STOP and a subsequent START
 * condition, split operations are broken down into multiple I2C transfers. If the
 * above operations are performed, it will result in setting bit [6](tx_abort) of
 * the Raw Interrupt Status Register.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description           
 * :--------------------------------|:------|:-----------------------
 *  ALT_I2C_CON_IC_RESTART_EN_E_DIS | 0x0   | restart master disable
 *  ALT_I2C_CON_IC_RESTART_EN_E_EN  | 0x1   | restart master enable 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_CON_IC_RESTART_EN
 * 
 * restart master disable
 */
#define ALT_I2C_CON_IC_RESTART_EN_E_DIS 0x0
/*
 * Enumerated value for register field ALT_I2C_CON_IC_RESTART_EN
 * 
 * restart master enable
 */
#define ALT_I2C_CON_IC_RESTART_EN_E_EN  0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_CON_IC_RESTART_EN register field. */
#define ALT_I2C_CON_IC_RESTART_EN_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_I2C_CON_IC_RESTART_EN register field. */
#define ALT_I2C_CON_IC_RESTART_EN_MSB        5
/* The width in bits of the ALT_I2C_CON_IC_RESTART_EN register field. */
#define ALT_I2C_CON_IC_RESTART_EN_WIDTH      1
/* The mask used to set the ALT_I2C_CON_IC_RESTART_EN register field value. */
#define ALT_I2C_CON_IC_RESTART_EN_SET_MSK    0x00000020
/* The mask used to clear the ALT_I2C_CON_IC_RESTART_EN register field value. */
#define ALT_I2C_CON_IC_RESTART_EN_CLR_MSK    0xffffffdf
/* The reset value of the ALT_I2C_CON_IC_RESTART_EN register field. */
#define ALT_I2C_CON_IC_RESTART_EN_RESET      0x1
/* Extracts the ALT_I2C_CON_IC_RESTART_EN field value from a register. */
#define ALT_I2C_CON_IC_RESTART_EN_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_I2C_CON_IC_RESTART_EN register field value suitable for setting the register. */
#define ALT_I2C_CON_IC_RESTART_EN_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Slave Disable - ic_slave_disable
 * 
 * This bit controls whether I2C has its slave disabled. The slave will be
 * disabled, after reset.
 * 
 * NOTE: Software should ensure that if this bit is written with 0, then bit [0] of
 * this register should also be written with a 0.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description  
 * :-----------------------------|:------|:--------------
 *  ALT_I2C_CON_IC_SLV_DIS_E_DIS | 0x1   | slave disable
 *  ALT_I2C_CON_IC_SLV_DIS_E_EN  | 0x0   | slave enable 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_CON_IC_SLV_DIS
 * 
 * slave disable
 */
#define ALT_I2C_CON_IC_SLV_DIS_E_DIS    0x1
/*
 * Enumerated value for register field ALT_I2C_CON_IC_SLV_DIS
 * 
 * slave enable
 */
#define ALT_I2C_CON_IC_SLV_DIS_E_EN     0x0

/* The Least Significant Bit (LSB) position of the ALT_I2C_CON_IC_SLV_DIS register field. */
#define ALT_I2C_CON_IC_SLV_DIS_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_I2C_CON_IC_SLV_DIS register field. */
#define ALT_I2C_CON_IC_SLV_DIS_MSB        6
/* The width in bits of the ALT_I2C_CON_IC_SLV_DIS register field. */
#define ALT_I2C_CON_IC_SLV_DIS_WIDTH      1
/* The mask used to set the ALT_I2C_CON_IC_SLV_DIS register field value. */
#define ALT_I2C_CON_IC_SLV_DIS_SET_MSK    0x00000040
/* The mask used to clear the ALT_I2C_CON_IC_SLV_DIS register field value. */
#define ALT_I2C_CON_IC_SLV_DIS_CLR_MSK    0xffffffbf
/* The reset value of the ALT_I2C_CON_IC_SLV_DIS register field. */
#define ALT_I2C_CON_IC_SLV_DIS_RESET      0x1
/* Extracts the ALT_I2C_CON_IC_SLV_DIS field value from a register. */
#define ALT_I2C_CON_IC_SLV_DIS_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_I2C_CON_IC_SLV_DIS register field value suitable for setting the register. */
#define ALT_I2C_CON_IC_SLV_DIS_SET(value) (((value) << 6) & 0x00000040)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_CON.
 */
struct ALT_I2C_CON_s
{
    uint32_t  master_mode         :  1;  /* Master Enable */
    uint32_t  speed               :  2;  /* Master Speed Control */
    uint32_t  ic_10bitaddr_slave  :  1;  /* Slave Address Size */
    uint32_t  ic_10bitaddr_master :  1;  /* Master Address Size */
    uint32_t  ic_restart_en       :  1;  /* Restart Enable */
    uint32_t  ic_slave_disable    :  1;  /* Slave Disable */
    uint32_t                      : 25;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_CON. */
typedef volatile struct ALT_I2C_CON_s  ALT_I2C_CON_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_CON register from the beginning of the component. */
#define ALT_I2C_CON_OFST        0x0
/* The address of the ALT_I2C_CON register. */
#define ALT_I2C_CON_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_CON_OFST))

/*
 * Register : Target Address Register - ic_tar
 * 
 * This register can be written to only when the ic_enable register is set to 0.
 * This register is 13 bits wide. All bits can be dynamically updated as long as
 * any set of the following conditions are true,
 * 
 * (Enable Register bit 0 is set to 0) or (Enable Register bit 0 is set to 1 AND
 * (I2C is NOT engaged in any Master [tx, rx] operation [ic_status register
 * mst_activity bit 5 is set to 0]) AND (I2C is enabled to operate in Master
 * mode[ic_con bit[0] is set to one]) AND (there are NO entries in the TX FIFO
 * Register [IC_STATUS bit [2] is set to 1])
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                  
 * :--------|:-------|:------|:------------------------------
 *  [9:0]   | RW     | 0x55  | Master Target Address        
 *  [10]    | RW     | 0x0   | General Call OR Start        
 *  [11]    | RW     | 0x0   | Special                      
 *  [12]    | RW     | 0x1   | Master Addressing Bit Control
 *  [31:13] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : Master Target Address - ic_tar
 * 
 * This is the target address for any master transaction. When transmitting a
 * General Call, these bits are ignored. To generate a START BYTE, the CPU needs to
 * write only once into these bits. If the ic_tar and ic_sar are the same, loopback
 * exists but the FIFOs are shared between master and slave, so full loopback is
 * not feasible. Only one direction loopback mode is supported (simplex), not
 * duplex. A master cannot transmit to itself; it can transmit to only a slave.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TAR_IC_TAR register field. */
#define ALT_I2C_TAR_IC_TAR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_TAR_IC_TAR register field. */
#define ALT_I2C_TAR_IC_TAR_MSB        9
/* The width in bits of the ALT_I2C_TAR_IC_TAR register field. */
#define ALT_I2C_TAR_IC_TAR_WIDTH      10
/* The mask used to set the ALT_I2C_TAR_IC_TAR register field value. */
#define ALT_I2C_TAR_IC_TAR_SET_MSK    0x000003ff
/* The mask used to clear the ALT_I2C_TAR_IC_TAR register field value. */
#define ALT_I2C_TAR_IC_TAR_CLR_MSK    0xfffffc00
/* The reset value of the ALT_I2C_TAR_IC_TAR register field. */
#define ALT_I2C_TAR_IC_TAR_RESET      0x55
/* Extracts the ALT_I2C_TAR_IC_TAR field value from a register. */
#define ALT_I2C_TAR_IC_TAR_GET(value) (((value) & 0x000003ff) >> 0)
/* Produces a ALT_I2C_TAR_IC_TAR register field value suitable for setting the register. */
#define ALT_I2C_TAR_IC_TAR_SET(value) (((value) << 0) & 0x000003ff)

/*
 * Field : General Call OR Start - gc_or_start
 * 
 * If bit 11 (SPECIAL) of this Register is set to 1, then this bit indicates
 * whether a General Call or START byte command is to be performed by the I2C or
 * General Call Address after issuing a General Call, only writes may be performed.
 * Attempting to issue a read command results in setting bit 6 (TX_ABRT) of the Raw
 * Interrupt_Status register. The I2C remains in General Call mode until the
 * special bit value (bit 11) is cleared.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description 
 * :------------------------------------|:------|:-------------
 *  ALT_I2C_TAR_GC_OR_START_E_GENCALL   | 0x0   | General Call
 *  ALT_I2C_TAR_GC_OR_START_E_STARTBYTE | 0x1   | START Byte  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_TAR_GC_OR_START
 * 
 * General Call
 */
#define ALT_I2C_TAR_GC_OR_START_E_GENCALL   0x0
/*
 * Enumerated value for register field ALT_I2C_TAR_GC_OR_START
 * 
 * START Byte
 */
#define ALT_I2C_TAR_GC_OR_START_E_STARTBYTE 0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_TAR_GC_OR_START register field. */
#define ALT_I2C_TAR_GC_OR_START_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_I2C_TAR_GC_OR_START register field. */
#define ALT_I2C_TAR_GC_OR_START_MSB        10
/* The width in bits of the ALT_I2C_TAR_GC_OR_START register field. */
#define ALT_I2C_TAR_GC_OR_START_WIDTH      1
/* The mask used to set the ALT_I2C_TAR_GC_OR_START register field value. */
#define ALT_I2C_TAR_GC_OR_START_SET_MSK    0x00000400
/* The mask used to clear the ALT_I2C_TAR_GC_OR_START register field value. */
#define ALT_I2C_TAR_GC_OR_START_CLR_MSK    0xfffffbff
/* The reset value of the ALT_I2C_TAR_GC_OR_START register field. */
#define ALT_I2C_TAR_GC_OR_START_RESET      0x0
/* Extracts the ALT_I2C_TAR_GC_OR_START field value from a register. */
#define ALT_I2C_TAR_GC_OR_START_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_I2C_TAR_GC_OR_START register field value suitable for setting the register. */
#define ALT_I2C_TAR_GC_OR_START_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Special - special
 * 
 * This bit indicates whether software performs a General Call or START BYTE
 * command.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description                                
 * :--------------------------------|:------|:--------------------------------------------
 *  ALT_I2C_TAR_SPECIAL_E_GENCALL   | 0x0   | Ignore bit 10 gc_or_start and use ic_tar   
 * :                                |       | normally                                   
 *  ALT_I2C_TAR_SPECIAL_E_STARTBYTE | 0x1   | Perform special I2C command as specified in
 * :                                |       | gc_or_start                                
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_TAR_SPECIAL
 * 
 * Ignore bit 10 gc_or_start and use ic_tar normally
 */
#define ALT_I2C_TAR_SPECIAL_E_GENCALL   0x0
/*
 * Enumerated value for register field ALT_I2C_TAR_SPECIAL
 * 
 * Perform special I2C command as specified in gc_or_start
 */
#define ALT_I2C_TAR_SPECIAL_E_STARTBYTE 0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_TAR_SPECIAL register field. */
#define ALT_I2C_TAR_SPECIAL_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_I2C_TAR_SPECIAL register field. */
#define ALT_I2C_TAR_SPECIAL_MSB        11
/* The width in bits of the ALT_I2C_TAR_SPECIAL register field. */
#define ALT_I2C_TAR_SPECIAL_WIDTH      1
/* The mask used to set the ALT_I2C_TAR_SPECIAL register field value. */
#define ALT_I2C_TAR_SPECIAL_SET_MSK    0x00000800
/* The mask used to clear the ALT_I2C_TAR_SPECIAL register field value. */
#define ALT_I2C_TAR_SPECIAL_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_I2C_TAR_SPECIAL register field. */
#define ALT_I2C_TAR_SPECIAL_RESET      0x0
/* Extracts the ALT_I2C_TAR_SPECIAL field value from a register. */
#define ALT_I2C_TAR_SPECIAL_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_I2C_TAR_SPECIAL register field value suitable for setting the register. */
#define ALT_I2C_TAR_SPECIAL_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : Master Addressing Bit Control - ic_10bitaddr_master
 * 
 * This bit controls whether the i2c starts its transfers in 7-bit or 10-bit
 * addressing mode when acting as a master.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description          
 * :---------------------------------------|:------|:----------------------
 *  ALT_I2C_TAR_IC_10BITADDR_MST_E_START7  | 0x0   | Master Address, 7bit 
 *  ALT_I2C_TAR_IC_10BITADDR_MST_E_START10 | 0x1   | Master Address, 10bit
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_TAR_IC_10BITADDR_MST
 * 
 * Master Address, 7bit
 */
#define ALT_I2C_TAR_IC_10BITADDR_MST_E_START7   0x0
/*
 * Enumerated value for register field ALT_I2C_TAR_IC_10BITADDR_MST
 * 
 * Master Address, 10bit
 */
#define ALT_I2C_TAR_IC_10BITADDR_MST_E_START10  0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_TAR_IC_10BITADDR_MST register field. */
#define ALT_I2C_TAR_IC_10BITADDR_MST_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_I2C_TAR_IC_10BITADDR_MST register field. */
#define ALT_I2C_TAR_IC_10BITADDR_MST_MSB        12
/* The width in bits of the ALT_I2C_TAR_IC_10BITADDR_MST register field. */
#define ALT_I2C_TAR_IC_10BITADDR_MST_WIDTH      1
/* The mask used to set the ALT_I2C_TAR_IC_10BITADDR_MST register field value. */
#define ALT_I2C_TAR_IC_10BITADDR_MST_SET_MSK    0x00001000
/* The mask used to clear the ALT_I2C_TAR_IC_10BITADDR_MST register field value. */
#define ALT_I2C_TAR_IC_10BITADDR_MST_CLR_MSK    0xffffefff
/* The reset value of the ALT_I2C_TAR_IC_10BITADDR_MST register field. */
#define ALT_I2C_TAR_IC_10BITADDR_MST_RESET      0x1
/* Extracts the ALT_I2C_TAR_IC_10BITADDR_MST field value from a register. */
#define ALT_I2C_TAR_IC_10BITADDR_MST_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_I2C_TAR_IC_10BITADDR_MST register field value suitable for setting the register. */
#define ALT_I2C_TAR_IC_10BITADDR_MST_SET(value) (((value) << 12) & 0x00001000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_TAR.
 */
struct ALT_I2C_TAR_s
{
    uint32_t  ic_tar              : 10;  /* Master Target Address */
    uint32_t  gc_or_start         :  1;  /* General Call OR Start */
    uint32_t  special             :  1;  /* Special */
    uint32_t  ic_10bitaddr_master :  1;  /* Master Addressing Bit Control */
    uint32_t                      : 19;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_TAR. */
typedef volatile struct ALT_I2C_TAR_s  ALT_I2C_TAR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_TAR register from the beginning of the component. */
#define ALT_I2C_TAR_OFST        0x4
/* The address of the ALT_I2C_TAR register. */
#define ALT_I2C_TAR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_TAR_OFST))

/*
 * Register : Slave Address Register - ic_sar
 * 
 * Holds Address of Slave
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description  
 * :--------|:-------|:------|:--------------
 *  [9:0]   | RW     | 0x55  | Slave Address
 *  [31:10] | ???    | 0x0   | *UNDEFINED*  
 * 
 */
/*
 * Field : Slave Address - ic_sar
 * 
 * The Slave Address register holds the slave address when the I2C is operating as
 * a slave. For 7-bit addressing, only Field Bits [6:0] of the Slave Address
 * Register are used. This register can be written only when the I2C interface is
 * disabled, which corresponds to field bit 0 of the Enable Register being set to
 * 0. Writes at other times have no effect.
 * 
 * Note, the default values cannot be any of the reserved address locations: that
 * is,
 * 
 * 0x00 to 0x07, or 0x78 to 0x7f. The correct operation of the device is not
 * guaranteed if you program the Slave Address Register or Target Address Register
 * to a reserved value.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_SAR_IC_SAR register field. */
#define ALT_I2C_SAR_IC_SAR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_SAR_IC_SAR register field. */
#define ALT_I2C_SAR_IC_SAR_MSB        9
/* The width in bits of the ALT_I2C_SAR_IC_SAR register field. */
#define ALT_I2C_SAR_IC_SAR_WIDTH      10
/* The mask used to set the ALT_I2C_SAR_IC_SAR register field value. */
#define ALT_I2C_SAR_IC_SAR_SET_MSK    0x000003ff
/* The mask used to clear the ALT_I2C_SAR_IC_SAR register field value. */
#define ALT_I2C_SAR_IC_SAR_CLR_MSK    0xfffffc00
/* The reset value of the ALT_I2C_SAR_IC_SAR register field. */
#define ALT_I2C_SAR_IC_SAR_RESET      0x55
/* Extracts the ALT_I2C_SAR_IC_SAR field value from a register. */
#define ALT_I2C_SAR_IC_SAR_GET(value) (((value) & 0x000003ff) >> 0)
/* Produces a ALT_I2C_SAR_IC_SAR register field value suitable for setting the register. */
#define ALT_I2C_SAR_IC_SAR_SET(value) (((value) << 0) & 0x000003ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_SAR.
 */
struct ALT_I2C_SAR_s
{
    uint32_t  ic_sar : 10;  /* Slave Address */
    uint32_t         : 22;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_SAR. */
typedef volatile struct ALT_I2C_SAR_s  ALT_I2C_SAR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_SAR register from the beginning of the component. */
#define ALT_I2C_SAR_OFST        0x8
/* The address of the ALT_I2C_SAR register. */
#define ALT_I2C_SAR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_SAR_OFST))

/*
 * Register : Tx Rx Data and Command Register - ic_data_cmd
 * 
 * This is the register the CPU writes to when filling the TX FIFO. Reading from
 * this register returns bytes from RX FIFO.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description              
 * :--------|:-------|:------|:--------------------------
 *  [7:0]   | RW     | 0x0   | Tx Rx Data               
 *  [8]     | W      | 0x0   | Master Read Write Control
 *  [9]     | W      | 0x0   | Generate Stop            
 *  [10]    | W      | 0x0   | Generate Restart         
 *  [31:11] | ???    | 0x0   | *UNDEFINED*              
 * 
 */
/*
 * Field : Tx Rx Data - dat
 * 
 * This Field  contains the data to be transmitted or received on the I2C bus. If
 * you are writing to these bits and want to perform a read, bits 7:0 (dat) are
 * ignored by the I2C. However, when you read from this register, these bits return
 * the value of data received on the I2C interface.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_DATA_CMD_DAT register field. */
#define ALT_I2C_DATA_CMD_DAT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_DATA_CMD_DAT register field. */
#define ALT_I2C_DATA_CMD_DAT_MSB        7
/* The width in bits of the ALT_I2C_DATA_CMD_DAT register field. */
#define ALT_I2C_DATA_CMD_DAT_WIDTH      8
/* The mask used to set the ALT_I2C_DATA_CMD_DAT register field value. */
#define ALT_I2C_DATA_CMD_DAT_SET_MSK    0x000000ff
/* The mask used to clear the ALT_I2C_DATA_CMD_DAT register field value. */
#define ALT_I2C_DATA_CMD_DAT_CLR_MSK    0xffffff00
/* The reset value of the ALT_I2C_DATA_CMD_DAT register field. */
#define ALT_I2C_DATA_CMD_DAT_RESET      0x0
/* Extracts the ALT_I2C_DATA_CMD_DAT field value from a register. */
#define ALT_I2C_DATA_CMD_DAT_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_I2C_DATA_CMD_DAT register field value suitable for setting the register. */
#define ALT_I2C_DATA_CMD_DAT_SET(value) (((value) << 0) & 0x000000ff)

/*
 * Field : Master Read Write Control - cmd
 * 
 * This bit controls whether a read or a write is performed. This bit does not
 * control the direction when the I2C acts as a slave. It controls only the
 * direction when it acts as a master. When a command is entered in the TX FIFO,
 * this bit distinguishes the write and read commands. In slave-receiver mode, this
 * bit is a 'don't care' because writes to this register are not required. In
 * slave-transmitter mode, a '0' indicates that the CPU data is to be transmitted.
 * When programming this bit, you should remember the following: attempting to
 * perform a read operation after a General Call command has been sent results in a
 * tx_abrt interrupt (bit 6 of the Raw Intr Status Register), unless bit 11 special
 * in the Target Address Register has been cleared. If a '1' is written to this bit
 * after receiving a RD_REQ interrupt, then a tx_abrt interrupt occurs.
 * 
 * NOTE: It is possible that while attempting a master I2C read transfer on I2C, a
 * RD_REQ interrupt may have occurred simultaneously due to a remote I2C master
 * addressing I2C. In this type of scenario, I2C ignores the Data Cmd write,
 * generates a tx_abrt interrupt, and waits to service the RD_REQ interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description 
 * :--------------------------|:------|:-------------
 *  ALT_I2C_DATA_CMD_CMD_E_RD | 0x1   | Master Read 
 *  ALT_I2C_DATA_CMD_CMD_E_WR | 0x0   | Master Write
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_DATA_CMD_CMD
 * 
 * Master Read
 */
#define ALT_I2C_DATA_CMD_CMD_E_RD   0x1
/*
 * Enumerated value for register field ALT_I2C_DATA_CMD_CMD
 * 
 * Master Write
 */
#define ALT_I2C_DATA_CMD_CMD_E_WR   0x0

/* The Least Significant Bit (LSB) position of the ALT_I2C_DATA_CMD_CMD register field. */
#define ALT_I2C_DATA_CMD_CMD_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_I2C_DATA_CMD_CMD register field. */
#define ALT_I2C_DATA_CMD_CMD_MSB        8
/* The width in bits of the ALT_I2C_DATA_CMD_CMD register field. */
#define ALT_I2C_DATA_CMD_CMD_WIDTH      1
/* The mask used to set the ALT_I2C_DATA_CMD_CMD register field value. */
#define ALT_I2C_DATA_CMD_CMD_SET_MSK    0x00000100
/* The mask used to clear the ALT_I2C_DATA_CMD_CMD register field value. */
#define ALT_I2C_DATA_CMD_CMD_CLR_MSK    0xfffffeff
/* The reset value of the ALT_I2C_DATA_CMD_CMD register field. */
#define ALT_I2C_DATA_CMD_CMD_RESET      0x0
/* Extracts the ALT_I2C_DATA_CMD_CMD field value from a register. */
#define ALT_I2C_DATA_CMD_CMD_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_I2C_DATA_CMD_CMD register field value suitable for setting the register. */
#define ALT_I2C_DATA_CMD_CMD_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Generate Stop - stop
 * 
 * This bit controls whether a STOP is issued after the byte is sent or received.
 * 
 * 1 = STOP is issued after this byte, regardless of whether or not the Tx FIFO is
 * empty. If the Tx FIFO is not empty, the master immediately tries to start a new
 * transfer by issuing a START and arbitrating for the bus.
 * 
 * 0 = STOP is not issued after this byte, regardless of whether or not the Tx FIFO
 * is empty. If the Tx FIFO is not empty, the master continues the current transfer
 * by sending/receiving data bytes according to the value of the CMD bit. If the Tx
 * FIFO is empty, the master holds the SCL line low and stalls the bus until a new
 * command is available in the Tx FIFO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description      
 * :--------------------------------|:------|:------------------
 *  ALT_I2C_DATA_CMD_STOP_E_STOP    | 0x1   | Issue Stop       
 *  ALT_I2C_DATA_CMD_STOP_E_NO_STOP | 0x0   | Do Not Issue Stop
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_DATA_CMD_STOP
 * 
 * Issue Stop
 */
#define ALT_I2C_DATA_CMD_STOP_E_STOP    0x1
/*
 * Enumerated value for register field ALT_I2C_DATA_CMD_STOP
 * 
 * Do Not Issue Stop
 */
#define ALT_I2C_DATA_CMD_STOP_E_NO_STOP 0x0

/* The Least Significant Bit (LSB) position of the ALT_I2C_DATA_CMD_STOP register field. */
#define ALT_I2C_DATA_CMD_STOP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_I2C_DATA_CMD_STOP register field. */
#define ALT_I2C_DATA_CMD_STOP_MSB        9
/* The width in bits of the ALT_I2C_DATA_CMD_STOP register field. */
#define ALT_I2C_DATA_CMD_STOP_WIDTH      1
/* The mask used to set the ALT_I2C_DATA_CMD_STOP register field value. */
#define ALT_I2C_DATA_CMD_STOP_SET_MSK    0x00000200
/* The mask used to clear the ALT_I2C_DATA_CMD_STOP register field value. */
#define ALT_I2C_DATA_CMD_STOP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_I2C_DATA_CMD_STOP register field. */
#define ALT_I2C_DATA_CMD_STOP_RESET      0x0
/* Extracts the ALT_I2C_DATA_CMD_STOP field value from a register. */
#define ALT_I2C_DATA_CMD_STOP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_I2C_DATA_CMD_STOP register field value suitable for setting the register. */
#define ALT_I2C_DATA_CMD_STOP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Generate Restart - restart
 * 
 * This bit controls whether a RESTART is issued before the byte is sent or
 * received.
 * 
 * 1 = A RESTART is issued before the data is sent/received (according to the value
 * of CMD), regardless of whether or not the transfer direction is changing from
 * the previous command.
 * 
 * 0 = A RESTART is issued only if the transfer direction is changing from the
 * previous command.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                             | Value | Description                      
 * :-------------------------------------------------|:------|:----------------------------------
 *  ALT_I2C_DATA_CMD_RESTART_E_RESTART               | 0x1   | Issue Restart                    
 *  ALT_I2C_DATA_CMD_RESTART_E_RESTART_ON_DIR_CHANGE | 0x0   | Issue Restart On Direction Change
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_DATA_CMD_RESTART
 * 
 * Issue Restart
 */
#define ALT_I2C_DATA_CMD_RESTART_E_RESTART                  0x1
/*
 * Enumerated value for register field ALT_I2C_DATA_CMD_RESTART
 * 
 * Issue Restart On Direction Change
 */
#define ALT_I2C_DATA_CMD_RESTART_E_RESTART_ON_DIR_CHANGE    0x0

/* The Least Significant Bit (LSB) position of the ALT_I2C_DATA_CMD_RESTART register field. */
#define ALT_I2C_DATA_CMD_RESTART_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_I2C_DATA_CMD_RESTART register field. */
#define ALT_I2C_DATA_CMD_RESTART_MSB        10
/* The width in bits of the ALT_I2C_DATA_CMD_RESTART register field. */
#define ALT_I2C_DATA_CMD_RESTART_WIDTH      1
/* The mask used to set the ALT_I2C_DATA_CMD_RESTART register field value. */
#define ALT_I2C_DATA_CMD_RESTART_SET_MSK    0x00000400
/* The mask used to clear the ALT_I2C_DATA_CMD_RESTART register field value. */
#define ALT_I2C_DATA_CMD_RESTART_CLR_MSK    0xfffffbff
/* The reset value of the ALT_I2C_DATA_CMD_RESTART register field. */
#define ALT_I2C_DATA_CMD_RESTART_RESET      0x0
/* Extracts the ALT_I2C_DATA_CMD_RESTART field value from a register. */
#define ALT_I2C_DATA_CMD_RESTART_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_I2C_DATA_CMD_RESTART register field value suitable for setting the register. */
#define ALT_I2C_DATA_CMD_RESTART_SET(value) (((value) << 10) & 0x00000400)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_DATA_CMD.
 */
struct ALT_I2C_DATA_CMD_s
{
    uint32_t  dat     :  8;  /* Tx Rx Data */
    uint32_t  cmd     :  1;  /* Master Read Write Control */
    uint32_t  stop    :  1;  /* Generate Stop */
    uint32_t  restart :  1;  /* Generate Restart */
    uint32_t          : 21;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_DATA_CMD. */
typedef volatile struct ALT_I2C_DATA_CMD_s  ALT_I2C_DATA_CMD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_DATA_CMD register from the beginning of the component. */
#define ALT_I2C_DATA_CMD_OFST        0x10
/* The address of the ALT_I2C_DATA_CMD register. */
#define ALT_I2C_DATA_CMD_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_DATA_CMD_OFST))

/*
 * Register : Std Spd Clock SCL HCNT Register - ic_ss_scl_hcnt
 * 
 * This register sets the SCL clock high-period count for standard speed.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description            
 * :--------|:-------|:------|:------------------------
 *  [15:0]  | RW     | 0x190 | Std Spd SCL High Period
 *  [31:16] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : Std Spd SCL High Period - ic_ss_scl_hcnt
 * 
 * This register must be set before any I2C bus transaction can take place to
 * ensure proper I/O timing. This field sets the SCL clock high-period count for
 * standard speed. This register can be written only when the I2C interface is
 * disabled which corresponds to the Enable Register being set to 0. Writes at
 * other times have no effect. The minimum valid value is 6; hardware prevents
 * values less than this being written, and if attempted results in 6 being set. It
 * is readable and writeable.
 * 
 * NOTE: This register must not be programmed to a value higher than 65525, because
 * I2C uses a 16-bit counter to flag an I2C bus idle condition when this counter
 * reaches a value of IC_SS_SCL_HCNT + 10.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT register field. */
#define ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT register field. */
#define ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT_MSB        15
/* The width in bits of the ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT register field. */
#define ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT_WIDTH      16
/* The mask used to set the ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT register field value. */
#define ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT register field value. */
#define ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT_CLR_MSK    0xffff0000
/* The reset value of the ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT register field. */
#define ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT_RESET      0x190
/* Extracts the ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT field value from a register. */
#define ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT register field value suitable for setting the register. */
#define ALT_I2C_SS_SCL_HCNT_IC_SS_SCL_HCNT_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_SS_SCL_HCNT.
 */
struct ALT_I2C_SS_SCL_HCNT_s
{
    uint32_t  ic_ss_scl_hcnt : 16;  /* Std Spd SCL High Period */
    uint32_t                 : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_SS_SCL_HCNT. */
typedef volatile struct ALT_I2C_SS_SCL_HCNT_s  ALT_I2C_SS_SCL_HCNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_SS_SCL_HCNT register from the beginning of the component. */
#define ALT_I2C_SS_SCL_HCNT_OFST        0x14
/* The address of the ALT_I2C_SS_SCL_HCNT register. */
#define ALT_I2C_SS_SCL_HCNT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_SS_SCL_HCNT_OFST))

/*
 * Register : Std Spd Clock SCL LCNT Register - ic_ss_scl_lcnt
 * 
 * This register sets the SCL clock low-period count for standard speed
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description           
 * :--------|:-------|:------|:-----------------------
 *  [15:0]  | RW     | 0x1d6 | Std Spd SCL Low Period
 *  [31:16] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : Std Spd SCL Low Period - ic_ss_scl_lcnt
 * 
 * This register must be set before any I2C bus transaction can take place to
 * ensure proper I/O timing. This field sets the SCL clock low period count for
 * standard speed. This register can be written only when the I2C interface is
 * disabled which corresponds to the Enable Register register being set to 0.
 * Writes at other times have no effect. The minimum valid value is 8; hardware
 * prevents values less than this from being written, and if attempted, results in
 * 8 being set.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT register field. */
#define ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT register field. */
#define ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT_MSB        15
/* The width in bits of the ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT register field. */
#define ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT_WIDTH      16
/* The mask used to set the ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT register field value. */
#define ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT register field value. */
#define ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT_CLR_MSK    0xffff0000
/* The reset value of the ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT register field. */
#define ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT_RESET      0x1d6
/* Extracts the ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT field value from a register. */
#define ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT register field value suitable for setting the register. */
#define ALT_I2C_SS_SCL_LCNT_IC_SS_SCL_LCNT_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_SS_SCL_LCNT.
 */
struct ALT_I2C_SS_SCL_LCNT_s
{
    uint32_t  ic_ss_scl_lcnt : 16;  /* Std Spd SCL Low Period */
    uint32_t                 : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_SS_SCL_LCNT. */
typedef volatile struct ALT_I2C_SS_SCL_LCNT_s  ALT_I2C_SS_SCL_LCNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_SS_SCL_LCNT register from the beginning of the component. */
#define ALT_I2C_SS_SCL_LCNT_OFST        0x18
/* The address of the ALT_I2C_SS_SCL_LCNT register. */
#define ALT_I2C_SS_SCL_LCNT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_SS_SCL_LCNT_OFST))

/*
 * Register : Fast Spd Clock SCL HCNT Register - ic_fs_scl_hcnt
 * 
 * This register sets the SCL clock high-period count for fast speed
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description             
 * :--------|:-------|:------|:-------------------------
 *  [15:0]  | RW     | 0x3c  | Fast Spd SCL High Period
 *  [31:16] | ???    | 0x0   | *UNDEFINED*             
 * 
 */
/*
 * Field : Fast Spd SCL High Period - ic_fs_scl_hcnt
 * 
 * This register must be set before any I2C bus transaction can take place to
 * ensure proper I/O timing. This register sets the SCL clock high-period count for
 * fast speed. It is used in high-speed mode to send the Master Code and START BYTE
 * or General CALL. This register goes away and becomes read-only returning 0s if
 * in Standard Speed Mode. This register can be written only when the I2C interface
 * is disabled, which corresponds to the Enable Register being set to 0. Writes at
 * other times have no effect. The minimum valid value is 6; hardware prevents
 * values less than this from being written, and if attempted results in 6 being
 * set.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT register field. */
#define ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT register field. */
#define ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT_MSB        15
/* The width in bits of the ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT register field. */
#define ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT_WIDTH      16
/* The mask used to set the ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT register field value. */
#define ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT register field value. */
#define ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT_CLR_MSK    0xffff0000
/* The reset value of the ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT register field. */
#define ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT_RESET      0x3c
/* Extracts the ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT field value from a register. */
#define ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT register field value suitable for setting the register. */
#define ALT_I2C_FS_SCL_HCNT_IC_FS_SCL_HCNT_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_FS_SCL_HCNT.
 */
struct ALT_I2C_FS_SCL_HCNT_s
{
    uint32_t  ic_fs_scl_hcnt : 16;  /* Fast Spd SCL High Period */
    uint32_t                 : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_FS_SCL_HCNT. */
typedef volatile struct ALT_I2C_FS_SCL_HCNT_s  ALT_I2C_FS_SCL_HCNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_FS_SCL_HCNT register from the beginning of the component. */
#define ALT_I2C_FS_SCL_HCNT_OFST        0x1c
/* The address of the ALT_I2C_FS_SCL_HCNT register. */
#define ALT_I2C_FS_SCL_HCNT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_FS_SCL_HCNT_OFST))

/*
 * Register : Fast Spd Clock SCL LCNT Register - ic_fs_scl_lcnt
 * 
 * This register sets the SCL clock low period count
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description            
 * :--------|:-------|:------|:------------------------
 *  [15:0]  | RW     | 0x82  | Fast Spd SCL Low Period
 *  [31:16] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : Fast Spd SCL Low Period - ic_fs_scl_lcnt
 * 
 * This register must be set before any I2C bus transaction can take place to
 * ensure proper I/O timing. This field sets the SCL clock low period count for
 * fast speed. It is used in high-speed mode to send the Master Code and START BYTE
 * or General CALL. This register can be written only when the I2C interface is
 * disabled, which corresponds to the Enable Register being set to 0. Writes at
 * other times have no effect.The minimum valid value is 8; hardware prevents
 * values less than this being written, and if attempted results in 8 being set.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT register field. */
#define ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT register field. */
#define ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT_MSB        15
/* The width in bits of the ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT register field. */
#define ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT_WIDTH      16
/* The mask used to set the ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT register field value. */
#define ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT register field value. */
#define ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT_CLR_MSK    0xffff0000
/* The reset value of the ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT register field. */
#define ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT_RESET      0x82
/* Extracts the ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT field value from a register. */
#define ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT register field value suitable for setting the register. */
#define ALT_I2C_FS_SCL_LCNT_IC_FS_SCL_LCNT_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_FS_SCL_LCNT.
 */
struct ALT_I2C_FS_SCL_LCNT_s
{
    uint32_t  ic_fs_scl_lcnt : 16;  /* Fast Spd SCL Low Period */
    uint32_t                 : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_FS_SCL_LCNT. */
typedef volatile struct ALT_I2C_FS_SCL_LCNT_s  ALT_I2C_FS_SCL_LCNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_FS_SCL_LCNT register from the beginning of the component. */
#define ALT_I2C_FS_SCL_LCNT_OFST        0x20
/* The address of the ALT_I2C_FS_SCL_LCNT register. */
#define ALT_I2C_FS_SCL_LCNT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_FS_SCL_LCNT_OFST))

/*
 * Register : Interrupt Status Register - ic_intr_stat
 * 
 * Each bit in this register has a corresponding mask bit in the Interrupt Mask
 * Register. These bits are cleared by reading the matching Interrupt Clear
 * Register. The unmasked raw versions of these bits are available in the Raw
 * Interrupt Status Register.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description             
 * :--------|:-------|:------|:-------------------------
 *  [0]     | R      | 0x0   | Receiver Under          
 *  [1]     | R      | 0x0   | Receiver Over           
 *  [2]     | R      | 0x0   | Receive Full            
 *  [3]     | R      | 0x0   | Interrupt Transmit Over 
 *  [4]     | R      | 0x0   | Interrupt Transmit Empty
 *  [5]     | R      | 0x0   | Interrupt Read Request  
 *  [6]     | R      | 0x0   | Interrupt TX Abort      
 *  [7]     | R      | 0x0   | Interrupt RX Done       
 *  [8]     | R      | 0x0   | Interrupt R_activity    
 *  [9]     | R      | 0x0   | Interrupt Stop Detect   
 *  [10]    | R      | 0x0   | Interrupt Start Detect  
 *  [11]    | R      | 0x0   | Interrupt General Call  
 *  [31:12] | ???    | 0x0   | *UNDEFINED*             
 * 
 */
/*
 * Field : Receiver Under - r_rx_under
 * 
 * Set if the processor attempts to read the receive buffer when it is empty by
 * reading from the Tx Rx Data and Command Register. If the module is disabled,
 * Enable Register is set to 0, this bit keeps its level until the master or slave
 * state machines go into idle, then this interrupt is cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_STAT_R_RX_UNDER register field. */
#define ALT_I2C_INTR_STAT_R_RX_UNDER_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_STAT_R_RX_UNDER register field. */
#define ALT_I2C_INTR_STAT_R_RX_UNDER_MSB        0
/* The width in bits of the ALT_I2C_INTR_STAT_R_RX_UNDER register field. */
#define ALT_I2C_INTR_STAT_R_RX_UNDER_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_STAT_R_RX_UNDER register field value. */
#define ALT_I2C_INTR_STAT_R_RX_UNDER_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_INTR_STAT_R_RX_UNDER register field value. */
#define ALT_I2C_INTR_STAT_R_RX_UNDER_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_INTR_STAT_R_RX_UNDER register field. */
#define ALT_I2C_INTR_STAT_R_RX_UNDER_RESET      0x0
/* Extracts the ALT_I2C_INTR_STAT_R_RX_UNDER field value from a register. */
#define ALT_I2C_INTR_STAT_R_RX_UNDER_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_INTR_STAT_R_RX_UNDER register field value suitable for setting the register. */
#define ALT_I2C_INTR_STAT_R_RX_UNDER_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Receiver Over - r_rx_over
 * 
 * Set if the receive buffer is completely filled to 64 and an additional byte is
 * received from an external I2C device. The I2C acknowledges this, but any data
 * bytes received after the FIFO is full are lost. If the module is disabled,
 * Enable Register bit[0] is set to 0 this bit keeps its level until the master or
 * slave state machines go into idle, then this interrupt is cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_STAT_R_RX_OVER register field. */
#define ALT_I2C_INTR_STAT_R_RX_OVER_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_STAT_R_RX_OVER register field. */
#define ALT_I2C_INTR_STAT_R_RX_OVER_MSB        1
/* The width in bits of the ALT_I2C_INTR_STAT_R_RX_OVER register field. */
#define ALT_I2C_INTR_STAT_R_RX_OVER_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_STAT_R_RX_OVER register field value. */
#define ALT_I2C_INTR_STAT_R_RX_OVER_SET_MSK    0x00000002
/* The mask used to clear the ALT_I2C_INTR_STAT_R_RX_OVER register field value. */
#define ALT_I2C_INTR_STAT_R_RX_OVER_CLR_MSK    0xfffffffd
/* The reset value of the ALT_I2C_INTR_STAT_R_RX_OVER register field. */
#define ALT_I2C_INTR_STAT_R_RX_OVER_RESET      0x0
/* Extracts the ALT_I2C_INTR_STAT_R_RX_OVER field value from a register. */
#define ALT_I2C_INTR_STAT_R_RX_OVER_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_I2C_INTR_STAT_R_RX_OVER register field value suitable for setting the register. */
#define ALT_I2C_INTR_STAT_R_RX_OVER_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Receive Full - r_rx_full
 * 
 * Set when the receive buffer reaches or goes above the Receive FIFO Threshold
 * Value(rx_tl). It is automatically cleared by hardware when buffer level goes
 * below the threshold. If the module is disabled, Bit [0] of the Enable Register
 * set to 0, the RX FIFO is flushed and held in reset; therefore the RX FIFO is not
 * full. So this bit is cleared once the Enable Register Bit 0 is programmed with a
 * 0, regardless of the activity that continues.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_STAT_R_RX_FULL register field. */
#define ALT_I2C_INTR_STAT_R_RX_FULL_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_STAT_R_RX_FULL register field. */
#define ALT_I2C_INTR_STAT_R_RX_FULL_MSB        2
/* The width in bits of the ALT_I2C_INTR_STAT_R_RX_FULL register field. */
#define ALT_I2C_INTR_STAT_R_RX_FULL_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_STAT_R_RX_FULL register field value. */
#define ALT_I2C_INTR_STAT_R_RX_FULL_SET_MSK    0x00000004
/* The mask used to clear the ALT_I2C_INTR_STAT_R_RX_FULL register field value. */
#define ALT_I2C_INTR_STAT_R_RX_FULL_CLR_MSK    0xfffffffb
/* The reset value of the ALT_I2C_INTR_STAT_R_RX_FULL register field. */
#define ALT_I2C_INTR_STAT_R_RX_FULL_RESET      0x0
/* Extracts the ALT_I2C_INTR_STAT_R_RX_FULL field value from a register. */
#define ALT_I2C_INTR_STAT_R_RX_FULL_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_I2C_INTR_STAT_R_RX_FULL register field value suitable for setting the register. */
#define ALT_I2C_INTR_STAT_R_RX_FULL_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Interrupt Transmit Over - r_tx_over
 * 
 * Set during transmit if the transmit buffer is filled to 64 and the processor
 * attempts to issue another I2C command by writing to the Data and Command
 * Register. When the module is disabled, this bit keeps its level until the master
 * or slave state machines goes into idle, then interrupt is cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_STAT_R_TX_OVER register field. */
#define ALT_I2C_INTR_STAT_R_TX_OVER_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_STAT_R_TX_OVER register field. */
#define ALT_I2C_INTR_STAT_R_TX_OVER_MSB        3
/* The width in bits of the ALT_I2C_INTR_STAT_R_TX_OVER register field. */
#define ALT_I2C_INTR_STAT_R_TX_OVER_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_STAT_R_TX_OVER register field value. */
#define ALT_I2C_INTR_STAT_R_TX_OVER_SET_MSK    0x00000008
/* The mask used to clear the ALT_I2C_INTR_STAT_R_TX_OVER register field value. */
#define ALT_I2C_INTR_STAT_R_TX_OVER_CLR_MSK    0xfffffff7
/* The reset value of the ALT_I2C_INTR_STAT_R_TX_OVER register field. */
#define ALT_I2C_INTR_STAT_R_TX_OVER_RESET      0x0
/* Extracts the ALT_I2C_INTR_STAT_R_TX_OVER field value from a register. */
#define ALT_I2C_INTR_STAT_R_TX_OVER_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_I2C_INTR_STAT_R_TX_OVER register field value suitable for setting the register. */
#define ALT_I2C_INTR_STAT_R_TX_OVER_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Interrupt Transmit Empty - r_tx_empty
 * 
 * This bit is set to 1 when the transmit buffer is at or below the threshold value
 * set in the ic_tx_tl register. It is automatically cleared by hardware when the
 * buffer level goes above the threshold. When the ic_enable bit 0 is 0, the TX
 * FIFO is flushed and held in reset. There the TX FIFO looks like it has no data
 * within it, so this bit is set to 1, provided there is activity in the master or
 * slave state machines. When there is no longer activity, this bit is set to 0.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_STAT_R_TX_EMPTY register field. */
#define ALT_I2C_INTR_STAT_R_TX_EMPTY_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_STAT_R_TX_EMPTY register field. */
#define ALT_I2C_INTR_STAT_R_TX_EMPTY_MSB        4
/* The width in bits of the ALT_I2C_INTR_STAT_R_TX_EMPTY register field. */
#define ALT_I2C_INTR_STAT_R_TX_EMPTY_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_STAT_R_TX_EMPTY register field value. */
#define ALT_I2C_INTR_STAT_R_TX_EMPTY_SET_MSK    0x00000010
/* The mask used to clear the ALT_I2C_INTR_STAT_R_TX_EMPTY register field value. */
#define ALT_I2C_INTR_STAT_R_TX_EMPTY_CLR_MSK    0xffffffef
/* The reset value of the ALT_I2C_INTR_STAT_R_TX_EMPTY register field. */
#define ALT_I2C_INTR_STAT_R_TX_EMPTY_RESET      0x0
/* Extracts the ALT_I2C_INTR_STAT_R_TX_EMPTY field value from a register. */
#define ALT_I2C_INTR_STAT_R_TX_EMPTY_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_I2C_INTR_STAT_R_TX_EMPTY register field value suitable for setting the register. */
#define ALT_I2C_INTR_STAT_R_TX_EMPTY_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Interrupt Read Request - r_rd_req
 * 
 * This bit is set to 1 when i2c is acting as a slave and another I2C master is
 * attempting to read data from I2C. The I2C holds the I2C bus in a wait state
 * (SCL=0) until this interrupt is serviced, which means that the slave has been
 * addressed by a remote master that is asking for data to be transferred. The
 * processor must respond to this interrupt and then write the requested data to
 * the IC_DATA_CMD register. This bit is set to 0 just after the processor reads
 * the ic_clr_rd_req register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_STAT_R_RD_REQ register field. */
#define ALT_I2C_INTR_STAT_R_RD_REQ_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_STAT_R_RD_REQ register field. */
#define ALT_I2C_INTR_STAT_R_RD_REQ_MSB        5
/* The width in bits of the ALT_I2C_INTR_STAT_R_RD_REQ register field. */
#define ALT_I2C_INTR_STAT_R_RD_REQ_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_STAT_R_RD_REQ register field value. */
#define ALT_I2C_INTR_STAT_R_RD_REQ_SET_MSK    0x00000020
/* The mask used to clear the ALT_I2C_INTR_STAT_R_RD_REQ register field value. */
#define ALT_I2C_INTR_STAT_R_RD_REQ_CLR_MSK    0xffffffdf
/* The reset value of the ALT_I2C_INTR_STAT_R_RD_REQ register field. */
#define ALT_I2C_INTR_STAT_R_RD_REQ_RESET      0x0
/* Extracts the ALT_I2C_INTR_STAT_R_RD_REQ field value from a register. */
#define ALT_I2C_INTR_STAT_R_RD_REQ_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_I2C_INTR_STAT_R_RD_REQ register field value suitable for setting the register. */
#define ALT_I2C_INTR_STAT_R_RD_REQ_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Interrupt TX Abort - r_tx_abrt
 * 
 * This bit indicates if I2C, as an I2C transmitter, is unable to complete the
 * intended actions on the contents of the transmit FIFO. This situation can occur
 * both as an I2C master or an I2C slave, and is referred to as a 'transmit
 * abort'.When this bit is set to 1, the ic_tx_abrt_source register indicates the
 * reason why the transmit abort takes places.
 * 
 * NOTE: The I2C flushes/resets/empties the TX FIFO whenever this bit is set. The
 * TX FIFO remains in this flushed state until the register ic_clr_tx_abrt is read.
 * Once this read is performed, the TX FIFO is then ready to accept more data bytes
 * from the APB interface.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_STAT_R_TX_ABRT register field. */
#define ALT_I2C_INTR_STAT_R_TX_ABRT_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_STAT_R_TX_ABRT register field. */
#define ALT_I2C_INTR_STAT_R_TX_ABRT_MSB        6
/* The width in bits of the ALT_I2C_INTR_STAT_R_TX_ABRT register field. */
#define ALT_I2C_INTR_STAT_R_TX_ABRT_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_STAT_R_TX_ABRT register field value. */
#define ALT_I2C_INTR_STAT_R_TX_ABRT_SET_MSK    0x00000040
/* The mask used to clear the ALT_I2C_INTR_STAT_R_TX_ABRT register field value. */
#define ALT_I2C_INTR_STAT_R_TX_ABRT_CLR_MSK    0xffffffbf
/* The reset value of the ALT_I2C_INTR_STAT_R_TX_ABRT register field. */
#define ALT_I2C_INTR_STAT_R_TX_ABRT_RESET      0x0
/* Extracts the ALT_I2C_INTR_STAT_R_TX_ABRT field value from a register. */
#define ALT_I2C_INTR_STAT_R_TX_ABRT_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_I2C_INTR_STAT_R_TX_ABRT register field value suitable for setting the register. */
#define ALT_I2C_INTR_STAT_R_TX_ABRT_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Interrupt RX Done - r_rx_done
 * 
 * When the I2C is acting as a slave-transmitter, this bit is set to 1, if the
 * master does not acknowledge a transmitted byte. This occurs on the last byte of
 * the transmission, indicating that the transmission is done.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_STAT_R_RX_DONE register field. */
#define ALT_I2C_INTR_STAT_R_RX_DONE_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_STAT_R_RX_DONE register field. */
#define ALT_I2C_INTR_STAT_R_RX_DONE_MSB        7
/* The width in bits of the ALT_I2C_INTR_STAT_R_RX_DONE register field. */
#define ALT_I2C_INTR_STAT_R_RX_DONE_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_STAT_R_RX_DONE register field value. */
#define ALT_I2C_INTR_STAT_R_RX_DONE_SET_MSK    0x00000080
/* The mask used to clear the ALT_I2C_INTR_STAT_R_RX_DONE register field value. */
#define ALT_I2C_INTR_STAT_R_RX_DONE_CLR_MSK    0xffffff7f
/* The reset value of the ALT_I2C_INTR_STAT_R_RX_DONE register field. */
#define ALT_I2C_INTR_STAT_R_RX_DONE_RESET      0x0
/* Extracts the ALT_I2C_INTR_STAT_R_RX_DONE field value from a register. */
#define ALT_I2C_INTR_STAT_R_RX_DONE_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_I2C_INTR_STAT_R_RX_DONE register field value suitable for setting the register. */
#define ALT_I2C_INTR_STAT_R_RX_DONE_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Interrupt R_activity - r_activity
 * 
 * This bit captures I2C activity and stays set until it is cleared. There are four
 * ways to clear it:
 * 
 * * Disabling the I2C
 * 
 * * Reading the ic_clr_activity register
 * 
 * * Reading the ic_clr_intr register
 * 
 * * I2C reset
 * 
 * Once this bit is set, it stays set unless one of the four methods is used to
 * clear it. Even if the I2C module is idle, this bit remains set until cleared,
 * indicating that there was activity on the bus.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_STAT_R_ACTIVITY register field. */
#define ALT_I2C_INTR_STAT_R_ACTIVITY_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_STAT_R_ACTIVITY register field. */
#define ALT_I2C_INTR_STAT_R_ACTIVITY_MSB        8
/* The width in bits of the ALT_I2C_INTR_STAT_R_ACTIVITY register field. */
#define ALT_I2C_INTR_STAT_R_ACTIVITY_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_STAT_R_ACTIVITY register field value. */
#define ALT_I2C_INTR_STAT_R_ACTIVITY_SET_MSK    0x00000100
/* The mask used to clear the ALT_I2C_INTR_STAT_R_ACTIVITY register field value. */
#define ALT_I2C_INTR_STAT_R_ACTIVITY_CLR_MSK    0xfffffeff
/* The reset value of the ALT_I2C_INTR_STAT_R_ACTIVITY register field. */
#define ALT_I2C_INTR_STAT_R_ACTIVITY_RESET      0x0
/* Extracts the ALT_I2C_INTR_STAT_R_ACTIVITY field value from a register. */
#define ALT_I2C_INTR_STAT_R_ACTIVITY_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_I2C_INTR_STAT_R_ACTIVITY register field value suitable for setting the register. */
#define ALT_I2C_INTR_STAT_R_ACTIVITY_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Interrupt Stop Detect - r_stop_det
 * 
 * Indicates whether a STOP condition has occurred on the I2C interface regardless
 * of whether I2C is operating in slave or master mode.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_STAT_R_STOP_DET register field. */
#define ALT_I2C_INTR_STAT_R_STOP_DET_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_STAT_R_STOP_DET register field. */
#define ALT_I2C_INTR_STAT_R_STOP_DET_MSB        9
/* The width in bits of the ALT_I2C_INTR_STAT_R_STOP_DET register field. */
#define ALT_I2C_INTR_STAT_R_STOP_DET_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_STAT_R_STOP_DET register field value. */
#define ALT_I2C_INTR_STAT_R_STOP_DET_SET_MSK    0x00000200
/* The mask used to clear the ALT_I2C_INTR_STAT_R_STOP_DET register field value. */
#define ALT_I2C_INTR_STAT_R_STOP_DET_CLR_MSK    0xfffffdff
/* The reset value of the ALT_I2C_INTR_STAT_R_STOP_DET register field. */
#define ALT_I2C_INTR_STAT_R_STOP_DET_RESET      0x0
/* Extracts the ALT_I2C_INTR_STAT_R_STOP_DET field value from a register. */
#define ALT_I2C_INTR_STAT_R_STOP_DET_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_I2C_INTR_STAT_R_STOP_DET register field value suitable for setting the register. */
#define ALT_I2C_INTR_STAT_R_STOP_DET_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Interrupt Start Detect - r_start_det
 * 
 * Indicates whether a START or RESTART condition has occurred on the I2C interface
 * regardless of whether I2C is operating in slave or master mode.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_STAT_R_START_DET register field. */
#define ALT_I2C_INTR_STAT_R_START_DET_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_STAT_R_START_DET register field. */
#define ALT_I2C_INTR_STAT_R_START_DET_MSB        10
/* The width in bits of the ALT_I2C_INTR_STAT_R_START_DET register field. */
#define ALT_I2C_INTR_STAT_R_START_DET_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_STAT_R_START_DET register field value. */
#define ALT_I2C_INTR_STAT_R_START_DET_SET_MSK    0x00000400
/* The mask used to clear the ALT_I2C_INTR_STAT_R_START_DET register field value. */
#define ALT_I2C_INTR_STAT_R_START_DET_CLR_MSK    0xfffffbff
/* The reset value of the ALT_I2C_INTR_STAT_R_START_DET register field. */
#define ALT_I2C_INTR_STAT_R_START_DET_RESET      0x0
/* Extracts the ALT_I2C_INTR_STAT_R_START_DET field value from a register. */
#define ALT_I2C_INTR_STAT_R_START_DET_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_I2C_INTR_STAT_R_START_DET register field value suitable for setting the register. */
#define ALT_I2C_INTR_STAT_R_START_DET_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Interrupt General Call - r_gen_call
 * 
 * Set only when a General Call address is received and it is acknowledged. It
 * stays set until it is cleared either by disabling I2C or when the CPU reads bit
 * 0 of the ic_clr_gen_call register. I2C stores the received data in the Rx
 * buffer.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_STAT_R_GEN_CALL register field. */
#define ALT_I2C_INTR_STAT_R_GEN_CALL_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_STAT_R_GEN_CALL register field. */
#define ALT_I2C_INTR_STAT_R_GEN_CALL_MSB        11
/* The width in bits of the ALT_I2C_INTR_STAT_R_GEN_CALL register field. */
#define ALT_I2C_INTR_STAT_R_GEN_CALL_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_STAT_R_GEN_CALL register field value. */
#define ALT_I2C_INTR_STAT_R_GEN_CALL_SET_MSK    0x00000800
/* The mask used to clear the ALT_I2C_INTR_STAT_R_GEN_CALL register field value. */
#define ALT_I2C_INTR_STAT_R_GEN_CALL_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_I2C_INTR_STAT_R_GEN_CALL register field. */
#define ALT_I2C_INTR_STAT_R_GEN_CALL_RESET      0x0
/* Extracts the ALT_I2C_INTR_STAT_R_GEN_CALL field value from a register. */
#define ALT_I2C_INTR_STAT_R_GEN_CALL_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_I2C_INTR_STAT_R_GEN_CALL register field value suitable for setting the register. */
#define ALT_I2C_INTR_STAT_R_GEN_CALL_SET(value) (((value) << 11) & 0x00000800)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_INTR_STAT.
 */
struct ALT_I2C_INTR_STAT_s
{
    const uint32_t  r_rx_under  :  1;  /* Receiver Under */
    const uint32_t  r_rx_over   :  1;  /* Receiver Over */
    const uint32_t  r_rx_full   :  1;  /* Receive Full */
    const uint32_t  r_tx_over   :  1;  /* Interrupt Transmit Over */
    const uint32_t  r_tx_empty  :  1;  /* Interrupt Transmit Empty */
    const uint32_t  r_rd_req    :  1;  /* Interrupt Read Request */
    const uint32_t  r_tx_abrt   :  1;  /* Interrupt TX Abort */
    const uint32_t  r_rx_done   :  1;  /* Interrupt RX Done */
    const uint32_t  r_activity  :  1;  /* Interrupt R_activity */
    const uint32_t  r_stop_det  :  1;  /* Interrupt Stop Detect */
    const uint32_t  r_start_det :  1;  /* Interrupt Start Detect */
    const uint32_t  r_gen_call  :  1;  /* Interrupt General Call */
    uint32_t                    : 20;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_INTR_STAT. */
typedef volatile struct ALT_I2C_INTR_STAT_s  ALT_I2C_INTR_STAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_INTR_STAT register from the beginning of the component. */
#define ALT_I2C_INTR_STAT_OFST        0x2c
/* The address of the ALT_I2C_INTR_STAT register. */
#define ALT_I2C_INTR_STAT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_INTR_STAT_OFST))

/*
 * Register : Interrupt Mask Register - ic_intr_mask
 * 
 * These bits mask their corresponding interrupt status bits.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description    
 * :--------|:-------|:------|:----------------
 *  [0]     | RW     | 0x1   | Mask RX Under  
 *  [1]     | RW     | 0x1   | RX Buffer Over 
 *  [2]     | RW     | 0x1   | RX Buffer Full 
 *  [3]     | RW     | 0x1   | TX Buffer Over 
 *  [4]     | RW     | 0x1   | TX Buffer Empty
 *  [5]     | RW     | 0x1   | Read Request   
 *  [6]     | RW     | 0x1   | TX Abort       
 *  [7]     | RW     | 0x1   | RX Done        
 *  [8]     | RW     | 0x0   | Activity Bit   
 *  [9]     | RW     | 0x0   | Stop Detect    
 *  [10]    | RW     | 0x0   | Start Detect   
 *  [11]    | RW     | 0x1   | General Call   
 *  [31:12] | ???    | 0x0   | *UNDEFINED*    
 * 
 */
/*
 * Field : Mask RX Under - m_rx_under
 * 
 * Set if the processor attempts to read the receive buffer when it is empty by
 * reading from the ic_data_cmd register. If the module is disabled ic_enable[0]=0,
 * this bit keeps its level until the master or slave state machines go into idle,
 * and then this interrupt is cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_MSK_M_RX_UNDER register field. */
#define ALT_I2C_INTR_MSK_M_RX_UNDER_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_MSK_M_RX_UNDER register field. */
#define ALT_I2C_INTR_MSK_M_RX_UNDER_MSB        0
/* The width in bits of the ALT_I2C_INTR_MSK_M_RX_UNDER register field. */
#define ALT_I2C_INTR_MSK_M_RX_UNDER_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_MSK_M_RX_UNDER register field value. */
#define ALT_I2C_INTR_MSK_M_RX_UNDER_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_INTR_MSK_M_RX_UNDER register field value. */
#define ALT_I2C_INTR_MSK_M_RX_UNDER_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_INTR_MSK_M_RX_UNDER register field. */
#define ALT_I2C_INTR_MSK_M_RX_UNDER_RESET      0x1
/* Extracts the ALT_I2C_INTR_MSK_M_RX_UNDER field value from a register. */
#define ALT_I2C_INTR_MSK_M_RX_UNDER_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_INTR_MSK_M_RX_UNDER register field value suitable for setting the register. */
#define ALT_I2C_INTR_MSK_M_RX_UNDER_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : RX Buffer Over - m_rx_over
 * 
 * Set if the receive buffer is completely filled to 64 and an additional byte is
 * received from an external I2C device. The I2C acknowledges this, but any data
 * bytes received after the FIFO is full are lost. If the module is disabled
 * ic_enable[0]=0, this bit keeps its level until the master or slave state
 * machines go into idle, then this interrupt is cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_MSK_M_RX_OVER register field. */
#define ALT_I2C_INTR_MSK_M_RX_OVER_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_MSK_M_RX_OVER register field. */
#define ALT_I2C_INTR_MSK_M_RX_OVER_MSB        1
/* The width in bits of the ALT_I2C_INTR_MSK_M_RX_OVER register field. */
#define ALT_I2C_INTR_MSK_M_RX_OVER_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_MSK_M_RX_OVER register field value. */
#define ALT_I2C_INTR_MSK_M_RX_OVER_SET_MSK    0x00000002
/* The mask used to clear the ALT_I2C_INTR_MSK_M_RX_OVER register field value. */
#define ALT_I2C_INTR_MSK_M_RX_OVER_CLR_MSK    0xfffffffd
/* The reset value of the ALT_I2C_INTR_MSK_M_RX_OVER register field. */
#define ALT_I2C_INTR_MSK_M_RX_OVER_RESET      0x1
/* Extracts the ALT_I2C_INTR_MSK_M_RX_OVER field value from a register. */
#define ALT_I2C_INTR_MSK_M_RX_OVER_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_I2C_INTR_MSK_M_RX_OVER register field value suitable for setting the register. */
#define ALT_I2C_INTR_MSK_M_RX_OVER_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : RX Buffer Full - m_rx_full
 * 
 * Set when the receive buffer reaches or goes above the RX_TL threshold in the
 * ic_rx_tl register. It is automatically cleared by hardware when buffer level
 * goes below the threshold. If the module is disabled ic_enable[0]=0, the RX FIFO
 * is flushed and held in reset; therefore the RX FIFO is not full. So this bit is
 * cleared once the ic_enable bit 0 is programmed with a 0, regardless of the
 * activity that continues.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_MSK_M_RX_FULL register field. */
#define ALT_I2C_INTR_MSK_M_RX_FULL_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_MSK_M_RX_FULL register field. */
#define ALT_I2C_INTR_MSK_M_RX_FULL_MSB        2
/* The width in bits of the ALT_I2C_INTR_MSK_M_RX_FULL register field. */
#define ALT_I2C_INTR_MSK_M_RX_FULL_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_MSK_M_RX_FULL register field value. */
#define ALT_I2C_INTR_MSK_M_RX_FULL_SET_MSK    0x00000004
/* The mask used to clear the ALT_I2C_INTR_MSK_M_RX_FULL register field value. */
#define ALT_I2C_INTR_MSK_M_RX_FULL_CLR_MSK    0xfffffffb
/* The reset value of the ALT_I2C_INTR_MSK_M_RX_FULL register field. */
#define ALT_I2C_INTR_MSK_M_RX_FULL_RESET      0x1
/* Extracts the ALT_I2C_INTR_MSK_M_RX_FULL field value from a register. */
#define ALT_I2C_INTR_MSK_M_RX_FULL_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_I2C_INTR_MSK_M_RX_FULL register field value suitable for setting the register. */
#define ALT_I2C_INTR_MSK_M_RX_FULL_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : TX Buffer Over - m_tx_over
 * 
 * Set during transmit if the transmit buffer is filled to 64 and the processor
 * attempts to issue another I2C command by writing to the ic_data_cmd register.
 * When the module is disabled, this bit keeps its level until the master or slave
 * state machines go into idle, then this interrupt is cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_MSK_M_TX_OVER register field. */
#define ALT_I2C_INTR_MSK_M_TX_OVER_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_MSK_M_TX_OVER register field. */
#define ALT_I2C_INTR_MSK_M_TX_OVER_MSB        3
/* The width in bits of the ALT_I2C_INTR_MSK_M_TX_OVER register field. */
#define ALT_I2C_INTR_MSK_M_TX_OVER_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_MSK_M_TX_OVER register field value. */
#define ALT_I2C_INTR_MSK_M_TX_OVER_SET_MSK    0x00000008
/* The mask used to clear the ALT_I2C_INTR_MSK_M_TX_OVER register field value. */
#define ALT_I2C_INTR_MSK_M_TX_OVER_CLR_MSK    0xfffffff7
/* The reset value of the ALT_I2C_INTR_MSK_M_TX_OVER register field. */
#define ALT_I2C_INTR_MSK_M_TX_OVER_RESET      0x1
/* Extracts the ALT_I2C_INTR_MSK_M_TX_OVER field value from a register. */
#define ALT_I2C_INTR_MSK_M_TX_OVER_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_I2C_INTR_MSK_M_TX_OVER register field value suitable for setting the register. */
#define ALT_I2C_INTR_MSK_M_TX_OVER_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : TX Buffer Empty - m_tx_empty
 * 
 * This bit is set to 1 when the transmit buffer is at or below the threshold value
 * set in the ic_tx_tl register. It is automatically cleared by hardware when the
 * buffer level goes above the threshold. When the ic_enable bit 0 is 0, the TX
 * FIFO is flushed and held in reset. There the TX FIFO looks like it has no data
 * within it, so this bit is set to 1, provided there is activity in the master or
 * slave state machines. When there is no longer activity, then this bit is set to
 * 0.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_MSK_M_TX_EMPTY register field. */
#define ALT_I2C_INTR_MSK_M_TX_EMPTY_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_MSK_M_TX_EMPTY register field. */
#define ALT_I2C_INTR_MSK_M_TX_EMPTY_MSB        4
/* The width in bits of the ALT_I2C_INTR_MSK_M_TX_EMPTY register field. */
#define ALT_I2C_INTR_MSK_M_TX_EMPTY_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_MSK_M_TX_EMPTY register field value. */
#define ALT_I2C_INTR_MSK_M_TX_EMPTY_SET_MSK    0x00000010
/* The mask used to clear the ALT_I2C_INTR_MSK_M_TX_EMPTY register field value. */
#define ALT_I2C_INTR_MSK_M_TX_EMPTY_CLR_MSK    0xffffffef
/* The reset value of the ALT_I2C_INTR_MSK_M_TX_EMPTY register field. */
#define ALT_I2C_INTR_MSK_M_TX_EMPTY_RESET      0x1
/* Extracts the ALT_I2C_INTR_MSK_M_TX_EMPTY field value from a register. */
#define ALT_I2C_INTR_MSK_M_TX_EMPTY_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_I2C_INTR_MSK_M_TX_EMPTY register field value suitable for setting the register. */
#define ALT_I2C_INTR_MSK_M_TX_EMPTY_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Read Request - m_rd_req
 * 
 * This bit is set to 1 when I2C is acting as a slave and another I2C master is
 * attempting to read data from I2C. The I2C holds the I2C bus in a wait state
 * (SCL=0) until this interrupt is serviced, which means that the slave has been
 * addressed by a remote master that is asking for data to be transferred. The
 * processor must respond to this interrupt and then write the requested data to
 * the ic_data_cmd register. This bit is set to 0 just after the processor reads
 * the ic_clr_rd_req register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_MSK_M_RD_REQ register field. */
#define ALT_I2C_INTR_MSK_M_RD_REQ_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_MSK_M_RD_REQ register field. */
#define ALT_I2C_INTR_MSK_M_RD_REQ_MSB        5
/* The width in bits of the ALT_I2C_INTR_MSK_M_RD_REQ register field. */
#define ALT_I2C_INTR_MSK_M_RD_REQ_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_MSK_M_RD_REQ register field value. */
#define ALT_I2C_INTR_MSK_M_RD_REQ_SET_MSK    0x00000020
/* The mask used to clear the ALT_I2C_INTR_MSK_M_RD_REQ register field value. */
#define ALT_I2C_INTR_MSK_M_RD_REQ_CLR_MSK    0xffffffdf
/* The reset value of the ALT_I2C_INTR_MSK_M_RD_REQ register field. */
#define ALT_I2C_INTR_MSK_M_RD_REQ_RESET      0x1
/* Extracts the ALT_I2C_INTR_MSK_M_RD_REQ field value from a register. */
#define ALT_I2C_INTR_MSK_M_RD_REQ_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_I2C_INTR_MSK_M_RD_REQ register field value suitable for setting the register. */
#define ALT_I2C_INTR_MSK_M_RD_REQ_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : TX Abort - m_tx_abrt
 * 
 * This bit indicates if I2C, as an I2C transmitter, is unable to complete the
 * intended actions on the contents of the transmit FIFO. This situation can occur
 * both as an I2C master or an I2C slave, and is referred to as a 'transmit abort'.
 * When this bit is set to 1, the ic_tx_abrt_source register indicates the reason
 * why the transmit abort takes places.
 * 
 * NOTE: The I2C flushes/resets/empties the TX FIFO whenever this bit is set. The
 * TX FIFO remains in this flushed state until the register ic_clr_tx_abrt is read.
 * Once this read is performed, the TX FIFO is then ready to accept more data bytes
 * from the APB interface.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_MSK_M_TX_ABRT register field. */
#define ALT_I2C_INTR_MSK_M_TX_ABRT_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_MSK_M_TX_ABRT register field. */
#define ALT_I2C_INTR_MSK_M_TX_ABRT_MSB        6
/* The width in bits of the ALT_I2C_INTR_MSK_M_TX_ABRT register field. */
#define ALT_I2C_INTR_MSK_M_TX_ABRT_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_MSK_M_TX_ABRT register field value. */
#define ALT_I2C_INTR_MSK_M_TX_ABRT_SET_MSK    0x00000040
/* The mask used to clear the ALT_I2C_INTR_MSK_M_TX_ABRT register field value. */
#define ALT_I2C_INTR_MSK_M_TX_ABRT_CLR_MSK    0xffffffbf
/* The reset value of the ALT_I2C_INTR_MSK_M_TX_ABRT register field. */
#define ALT_I2C_INTR_MSK_M_TX_ABRT_RESET      0x1
/* Extracts the ALT_I2C_INTR_MSK_M_TX_ABRT field value from a register. */
#define ALT_I2C_INTR_MSK_M_TX_ABRT_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_I2C_INTR_MSK_M_TX_ABRT register field value suitable for setting the register. */
#define ALT_I2C_INTR_MSK_M_TX_ABRT_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : RX Done - m_rx_done
 * 
 * When the I2C is acting as a slave-transmitter, this bit is set to 1, if the
 * master does not acknowledge a transmitted byte. This occurs on the last byte of
 * the transmission, indicating that the transmission is done.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_MSK_M_RX_DONE register field. */
#define ALT_I2C_INTR_MSK_M_RX_DONE_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_MSK_M_RX_DONE register field. */
#define ALT_I2C_INTR_MSK_M_RX_DONE_MSB        7
/* The width in bits of the ALT_I2C_INTR_MSK_M_RX_DONE register field. */
#define ALT_I2C_INTR_MSK_M_RX_DONE_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_MSK_M_RX_DONE register field value. */
#define ALT_I2C_INTR_MSK_M_RX_DONE_SET_MSK    0x00000080
/* The mask used to clear the ALT_I2C_INTR_MSK_M_RX_DONE register field value. */
#define ALT_I2C_INTR_MSK_M_RX_DONE_CLR_MSK    0xffffff7f
/* The reset value of the ALT_I2C_INTR_MSK_M_RX_DONE register field. */
#define ALT_I2C_INTR_MSK_M_RX_DONE_RESET      0x1
/* Extracts the ALT_I2C_INTR_MSK_M_RX_DONE field value from a register. */
#define ALT_I2C_INTR_MSK_M_RX_DONE_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_I2C_INTR_MSK_M_RX_DONE register field value suitable for setting the register. */
#define ALT_I2C_INTR_MSK_M_RX_DONE_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Activity Bit - m_activity
 * 
 * This bit captures i2c activity and stays set until it is cleared. There are four
 * ways to clear it:
 * 
 * * Disabling the i2c
 * 
 * * Reading the ic_clr_activity register
 * 
 * * Reading the ic_clr_intr register
 * 
 * * System reset
 * 
 * Once this bit is set, it stays set unless one of the four methods is used to
 * clear it. Even if the I2C module is idle, this bit remains set until cleared,
 * indicating that there was activity on the bus.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_MSK_M_ACTIVITY register field. */
#define ALT_I2C_INTR_MSK_M_ACTIVITY_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_MSK_M_ACTIVITY register field. */
#define ALT_I2C_INTR_MSK_M_ACTIVITY_MSB        8
/* The width in bits of the ALT_I2C_INTR_MSK_M_ACTIVITY register field. */
#define ALT_I2C_INTR_MSK_M_ACTIVITY_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_MSK_M_ACTIVITY register field value. */
#define ALT_I2C_INTR_MSK_M_ACTIVITY_SET_MSK    0x00000100
/* The mask used to clear the ALT_I2C_INTR_MSK_M_ACTIVITY register field value. */
#define ALT_I2C_INTR_MSK_M_ACTIVITY_CLR_MSK    0xfffffeff
/* The reset value of the ALT_I2C_INTR_MSK_M_ACTIVITY register field. */
#define ALT_I2C_INTR_MSK_M_ACTIVITY_RESET      0x0
/* Extracts the ALT_I2C_INTR_MSK_M_ACTIVITY field value from a register. */
#define ALT_I2C_INTR_MSK_M_ACTIVITY_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_I2C_INTR_MSK_M_ACTIVITY register field value suitable for setting the register. */
#define ALT_I2C_INTR_MSK_M_ACTIVITY_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Stop Detect - m_stop_det
 * 
 * Indicates whether a STOP condition has occurred on the I2C interface regardless
 * of whether i2c is operating in slave or master mode.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_MSK_M_STOP_DET register field. */
#define ALT_I2C_INTR_MSK_M_STOP_DET_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_MSK_M_STOP_DET register field. */
#define ALT_I2C_INTR_MSK_M_STOP_DET_MSB        9
/* The width in bits of the ALT_I2C_INTR_MSK_M_STOP_DET register field. */
#define ALT_I2C_INTR_MSK_M_STOP_DET_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_MSK_M_STOP_DET register field value. */
#define ALT_I2C_INTR_MSK_M_STOP_DET_SET_MSK    0x00000200
/* The mask used to clear the ALT_I2C_INTR_MSK_M_STOP_DET register field value. */
#define ALT_I2C_INTR_MSK_M_STOP_DET_CLR_MSK    0xfffffdff
/* The reset value of the ALT_I2C_INTR_MSK_M_STOP_DET register field. */
#define ALT_I2C_INTR_MSK_M_STOP_DET_RESET      0x0
/* Extracts the ALT_I2C_INTR_MSK_M_STOP_DET field value from a register. */
#define ALT_I2C_INTR_MSK_M_STOP_DET_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_I2C_INTR_MSK_M_STOP_DET register field value suitable for setting the register. */
#define ALT_I2C_INTR_MSK_M_STOP_DET_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Start Detect - m_start_det
 * 
 * Indicates whether a START or RESTART condition has occurred on the I2C interface
 * regardless of whether I2C is operating in slave or master mode.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_MSK_M_START_DET register field. */
#define ALT_I2C_INTR_MSK_M_START_DET_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_MSK_M_START_DET register field. */
#define ALT_I2C_INTR_MSK_M_START_DET_MSB        10
/* The width in bits of the ALT_I2C_INTR_MSK_M_START_DET register field. */
#define ALT_I2C_INTR_MSK_M_START_DET_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_MSK_M_START_DET register field value. */
#define ALT_I2C_INTR_MSK_M_START_DET_SET_MSK    0x00000400
/* The mask used to clear the ALT_I2C_INTR_MSK_M_START_DET register field value. */
#define ALT_I2C_INTR_MSK_M_START_DET_CLR_MSK    0xfffffbff
/* The reset value of the ALT_I2C_INTR_MSK_M_START_DET register field. */
#define ALT_I2C_INTR_MSK_M_START_DET_RESET      0x0
/* Extracts the ALT_I2C_INTR_MSK_M_START_DET field value from a register. */
#define ALT_I2C_INTR_MSK_M_START_DET_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_I2C_INTR_MSK_M_START_DET register field value suitable for setting the register. */
#define ALT_I2C_INTR_MSK_M_START_DET_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : General Call - m_gen_call
 * 
 * Set only when a General Call address is received and it is acknowledged. It
 * stays set until it is cleared either by disabling I2C or when the CPU reads bit
 * 0 of the ic_clr_gen_call register. I2C stores the received data in the Rx
 * buffer.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_INTR_MSK_M_GEN_CALL register field. */
#define ALT_I2C_INTR_MSK_M_GEN_CALL_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_I2C_INTR_MSK_M_GEN_CALL register field. */
#define ALT_I2C_INTR_MSK_M_GEN_CALL_MSB        11
/* The width in bits of the ALT_I2C_INTR_MSK_M_GEN_CALL register field. */
#define ALT_I2C_INTR_MSK_M_GEN_CALL_WIDTH      1
/* The mask used to set the ALT_I2C_INTR_MSK_M_GEN_CALL register field value. */
#define ALT_I2C_INTR_MSK_M_GEN_CALL_SET_MSK    0x00000800
/* The mask used to clear the ALT_I2C_INTR_MSK_M_GEN_CALL register field value. */
#define ALT_I2C_INTR_MSK_M_GEN_CALL_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_I2C_INTR_MSK_M_GEN_CALL register field. */
#define ALT_I2C_INTR_MSK_M_GEN_CALL_RESET      0x1
/* Extracts the ALT_I2C_INTR_MSK_M_GEN_CALL field value from a register. */
#define ALT_I2C_INTR_MSK_M_GEN_CALL_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_I2C_INTR_MSK_M_GEN_CALL register field value suitable for setting the register. */
#define ALT_I2C_INTR_MSK_M_GEN_CALL_SET(value) (((value) << 11) & 0x00000800)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_INTR_MSK.
 */
struct ALT_I2C_INTR_MSK_s
{
    uint32_t  m_rx_under  :  1;  /* Mask RX Under */
    uint32_t  m_rx_over   :  1;  /* RX Buffer Over */
    uint32_t  m_rx_full   :  1;  /* RX Buffer Full */
    uint32_t  m_tx_over   :  1;  /* TX Buffer Over */
    uint32_t  m_tx_empty  :  1;  /* TX Buffer Empty */
    uint32_t  m_rd_req    :  1;  /* Read Request */
    uint32_t  m_tx_abrt   :  1;  /* TX Abort */
    uint32_t  m_rx_done   :  1;  /* RX Done */
    uint32_t  m_activity  :  1;  /* Activity Bit */
    uint32_t  m_stop_det  :  1;  /* Stop Detect */
    uint32_t  m_start_det :  1;  /* Start Detect */
    uint32_t  m_gen_call  :  1;  /* General Call */
    uint32_t              : 20;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_INTR_MSK. */
typedef volatile struct ALT_I2C_INTR_MSK_s  ALT_I2C_INTR_MSK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_INTR_MSK register from the beginning of the component. */
#define ALT_I2C_INTR_MSK_OFST        0x30
/* The address of the ALT_I2C_INTR_MSK register. */
#define ALT_I2C_INTR_MSK_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_INTR_MSK_OFST))

/*
 * Register : Raw Interrupt Status Register - ic_raw_intr_stat
 * 
 * Unlike the ic_intr_stat register, these bits are not masked so they always show
 * the true status of the I2C.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description               
 * :--------|:-------|:------|:---------------------------
 *  [0]     | R      | 0x0   | I2C Raw Interrupt RX Under
 *  [1]     | R      | 0x0   | Raw Interrupt RX Over     
 *  [2]     | R      | 0x0   | Raw Interrupt RX Full     
 *  [3]     | R      | 0x0   | Raw Interrupt TX Over     
 *  [4]     | R      | 0x0   | Raw Interrupt TX Empty    
 *  [5]     | R      | 0x0   | Raw Interrupt Read Request
 *  [6]     | R      | 0x0   | Raw Interrupt TX Abort    
 *  [7]     | R      | 0x0   | Raw Interrupt RX Done     
 *  [8]     | R      | 0x0   | Raw Interrupt Activity    
 *  [9]     | R      | 0x0   | Raw Interrupt Stop Detect 
 *  [10]    | R      | 0x0   | Raw Interrupt Start Detect
 *  [11]    | R      | 0x0   | Raw Interrupt General Call
 *  [31:12] | ???    | 0x0   | *UNDEFINED*               
 * 
 */
/*
 * Field : I2C Raw Interrupt RX Under - rx_under
 * 
 * Set if the processor attempts to read the receive buffer when it is empty by
 * reading from the ic_data_cmd register. If the module is disabled ic_enable[0]=0,
 * this bit keeps its level until the master or slave state machines go into idle,
 * then this interrupt is cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_RAW_INTR_STAT_RX_UNDER register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_UNDER_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_RAW_INTR_STAT_RX_UNDER register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_UNDER_MSB        0
/* The width in bits of the ALT_I2C_RAW_INTR_STAT_RX_UNDER register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_UNDER_WIDTH      1
/* The mask used to set the ALT_I2C_RAW_INTR_STAT_RX_UNDER register field value. */
#define ALT_I2C_RAW_INTR_STAT_RX_UNDER_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_RAW_INTR_STAT_RX_UNDER register field value. */
#define ALT_I2C_RAW_INTR_STAT_RX_UNDER_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_RAW_INTR_STAT_RX_UNDER register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_UNDER_RESET      0x0
/* Extracts the ALT_I2C_RAW_INTR_STAT_RX_UNDER field value from a register. */
#define ALT_I2C_RAW_INTR_STAT_RX_UNDER_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_RAW_INTR_STAT_RX_UNDER register field value suitable for setting the register. */
#define ALT_I2C_RAW_INTR_STAT_RX_UNDER_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Raw Interrupt RX Over - rx_over
 * 
 * Set if the receive buffer is completely filled to  64 and an additional byte is
 * received from an external I2C device. The I2C acknowledges this, but any data
 * bytes received after the FIFO is full are lost. If the module is disabled
 * ic_enable[0]=0), this bit keeps its level until the master or slave state
 * machines go into then, this interrupt is cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_RAW_INTR_STAT_RX_OVER register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_OVER_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_I2C_RAW_INTR_STAT_RX_OVER register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_OVER_MSB        1
/* The width in bits of the ALT_I2C_RAW_INTR_STAT_RX_OVER register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_OVER_WIDTH      1
/* The mask used to set the ALT_I2C_RAW_INTR_STAT_RX_OVER register field value. */
#define ALT_I2C_RAW_INTR_STAT_RX_OVER_SET_MSK    0x00000002
/* The mask used to clear the ALT_I2C_RAW_INTR_STAT_RX_OVER register field value. */
#define ALT_I2C_RAW_INTR_STAT_RX_OVER_CLR_MSK    0xfffffffd
/* The reset value of the ALT_I2C_RAW_INTR_STAT_RX_OVER register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_OVER_RESET      0x0
/* Extracts the ALT_I2C_RAW_INTR_STAT_RX_OVER field value from a register. */
#define ALT_I2C_RAW_INTR_STAT_RX_OVER_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_I2C_RAW_INTR_STAT_RX_OVER register field value suitable for setting the register. */
#define ALT_I2C_RAW_INTR_STAT_RX_OVER_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Raw Interrupt RX Full - rx_full
 * 
 * Set when the receive buffer reaches or goes above the RX_TL threshold in the
 * ic_rx_tl register. It is automatically cleared by hardware when buffer level
 * goes below the threshold. If the module is disabled ic_enable[0]=0, the RX FIFO
 * is flushed and held in reset; therefore the RX FIFO is not full. So this bit is
 * cleared once the ic_enable bit 0 is programmed with a 0, regardless of the
 * activity that continues.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_RAW_INTR_STAT_RX_FULL register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_FULL_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_I2C_RAW_INTR_STAT_RX_FULL register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_FULL_MSB        2
/* The width in bits of the ALT_I2C_RAW_INTR_STAT_RX_FULL register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_FULL_WIDTH      1
/* The mask used to set the ALT_I2C_RAW_INTR_STAT_RX_FULL register field value. */
#define ALT_I2C_RAW_INTR_STAT_RX_FULL_SET_MSK    0x00000004
/* The mask used to clear the ALT_I2C_RAW_INTR_STAT_RX_FULL register field value. */
#define ALT_I2C_RAW_INTR_STAT_RX_FULL_CLR_MSK    0xfffffffb
/* The reset value of the ALT_I2C_RAW_INTR_STAT_RX_FULL register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_FULL_RESET      0x0
/* Extracts the ALT_I2C_RAW_INTR_STAT_RX_FULL field value from a register. */
#define ALT_I2C_RAW_INTR_STAT_RX_FULL_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_I2C_RAW_INTR_STAT_RX_FULL register field value suitable for setting the register. */
#define ALT_I2C_RAW_INTR_STAT_RX_FULL_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Raw Interrupt TX Over - tx_over
 * 
 * Set during transmit if the transmit buffer is filled to 64  and the processor
 * attempts to issue another I2C command by writing to the ic_data_cmd register.
 * When the module is disabled, this bit keeps its level until the master or slave
 * state machines go into idle, then this interrupt is cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_RAW_INTR_STAT_TX_OVER register field. */
#define ALT_I2C_RAW_INTR_STAT_TX_OVER_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_I2C_RAW_INTR_STAT_TX_OVER register field. */
#define ALT_I2C_RAW_INTR_STAT_TX_OVER_MSB        3
/* The width in bits of the ALT_I2C_RAW_INTR_STAT_TX_OVER register field. */
#define ALT_I2C_RAW_INTR_STAT_TX_OVER_WIDTH      1
/* The mask used to set the ALT_I2C_RAW_INTR_STAT_TX_OVER register field value. */
#define ALT_I2C_RAW_INTR_STAT_TX_OVER_SET_MSK    0x00000008
/* The mask used to clear the ALT_I2C_RAW_INTR_STAT_TX_OVER register field value. */
#define ALT_I2C_RAW_INTR_STAT_TX_OVER_CLR_MSK    0xfffffff7
/* The reset value of the ALT_I2C_RAW_INTR_STAT_TX_OVER register field. */
#define ALT_I2C_RAW_INTR_STAT_TX_OVER_RESET      0x0
/* Extracts the ALT_I2C_RAW_INTR_STAT_TX_OVER field value from a register. */
#define ALT_I2C_RAW_INTR_STAT_TX_OVER_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_I2C_RAW_INTR_STAT_TX_OVER register field value suitable for setting the register. */
#define ALT_I2C_RAW_INTR_STAT_TX_OVER_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Raw Interrupt TX Empty - tx_empty
 * 
 * This bit is set to 1 when the transmit buffer is at or below the threshold value
 * set in the ic_tx_tl register. It is automatically cleared by hardware when the
 * buffer level goes above the threshold. When the IC_ENABLE bit 0 is 0, the TX
 * FIFO is flushed and held in reset. There the TX FIFO looks like it has no data
 * within it, so this bit is set to 1, provided there is activity in the master or
 * slave state machines. When there is no longer activity, then this bit is set to
 * 0.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_RAW_INTR_STAT_TX_EMPTY register field. */
#define ALT_I2C_RAW_INTR_STAT_TX_EMPTY_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_I2C_RAW_INTR_STAT_TX_EMPTY register field. */
#define ALT_I2C_RAW_INTR_STAT_TX_EMPTY_MSB        4
/* The width in bits of the ALT_I2C_RAW_INTR_STAT_TX_EMPTY register field. */
#define ALT_I2C_RAW_INTR_STAT_TX_EMPTY_WIDTH      1
/* The mask used to set the ALT_I2C_RAW_INTR_STAT_TX_EMPTY register field value. */
#define ALT_I2C_RAW_INTR_STAT_TX_EMPTY_SET_MSK    0x00000010
/* The mask used to clear the ALT_I2C_RAW_INTR_STAT_TX_EMPTY register field value. */
#define ALT_I2C_RAW_INTR_STAT_TX_EMPTY_CLR_MSK    0xffffffef
/* The reset value of the ALT_I2C_RAW_INTR_STAT_TX_EMPTY register field. */
#define ALT_I2C_RAW_INTR_STAT_TX_EMPTY_RESET      0x0
/* Extracts the ALT_I2C_RAW_INTR_STAT_TX_EMPTY field value from a register. */
#define ALT_I2C_RAW_INTR_STAT_TX_EMPTY_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_I2C_RAW_INTR_STAT_TX_EMPTY register field value suitable for setting the register. */
#define ALT_I2C_RAW_INTR_STAT_TX_EMPTY_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Raw Interrupt Read Request - rd_req
 * 
 * This bit is set to 1 when I2C is acting as a slave and another I2C master is
 * attempting to read data from I2C. The i2c holds the I2C bus in a wait state
 * (SCL=0) until this interrupt is serviced, which means that the slave has been
 * addressed by a remote master that is asking for data to be transferred. The
 * processor must respond to this interrupt and then write the requested data to
 * the ic_data_cmd register. This bit is set to 0 just after the processor reads
 * the ic_clr_rd_req register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_RAW_INTR_STAT_RD_REQ register field. */
#define ALT_I2C_RAW_INTR_STAT_RD_REQ_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_I2C_RAW_INTR_STAT_RD_REQ register field. */
#define ALT_I2C_RAW_INTR_STAT_RD_REQ_MSB        5
/* The width in bits of the ALT_I2C_RAW_INTR_STAT_RD_REQ register field. */
#define ALT_I2C_RAW_INTR_STAT_RD_REQ_WIDTH      1
/* The mask used to set the ALT_I2C_RAW_INTR_STAT_RD_REQ register field value. */
#define ALT_I2C_RAW_INTR_STAT_RD_REQ_SET_MSK    0x00000020
/* The mask used to clear the ALT_I2C_RAW_INTR_STAT_RD_REQ register field value. */
#define ALT_I2C_RAW_INTR_STAT_RD_REQ_CLR_MSK    0xffffffdf
/* The reset value of the ALT_I2C_RAW_INTR_STAT_RD_REQ register field. */
#define ALT_I2C_RAW_INTR_STAT_RD_REQ_RESET      0x0
/* Extracts the ALT_I2C_RAW_INTR_STAT_RD_REQ field value from a register. */
#define ALT_I2C_RAW_INTR_STAT_RD_REQ_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_I2C_RAW_INTR_STAT_RD_REQ register field value suitable for setting the register. */
#define ALT_I2C_RAW_INTR_STAT_RD_REQ_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Raw Interrupt TX Abort - tx_abrt
 * 
 * This bit indicates if I2C, as an I2C transmitter, is unable to complete the
 * intended actions on the contents of the transmit FIFO. This situation can occur
 * both as an I2C master or an I2C slave, and is referred to as a 'transmit abort'.
 * When this bit is set to 1, the IC_TX_ABRT_SOURCE register indicates the reason
 * why the transmit abort takes places.
 * 
 * NOTE: The I2C flushes/resets/empties the TX FIFO whenever this bit is set. The
 * TX FIFO remains in this flushed state until the register ic_clr_tx_abrt is read.
 * Once this read is performed, the TX FIFO is then ready to accept more data bytes
 * from the APB interface.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_RAW_INTR_STAT_TX_ABRT register field. */
#define ALT_I2C_RAW_INTR_STAT_TX_ABRT_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_I2C_RAW_INTR_STAT_TX_ABRT register field. */
#define ALT_I2C_RAW_INTR_STAT_TX_ABRT_MSB        6
/* The width in bits of the ALT_I2C_RAW_INTR_STAT_TX_ABRT register field. */
#define ALT_I2C_RAW_INTR_STAT_TX_ABRT_WIDTH      1
/* The mask used to set the ALT_I2C_RAW_INTR_STAT_TX_ABRT register field value. */
#define ALT_I2C_RAW_INTR_STAT_TX_ABRT_SET_MSK    0x00000040
/* The mask used to clear the ALT_I2C_RAW_INTR_STAT_TX_ABRT register field value. */
#define ALT_I2C_RAW_INTR_STAT_TX_ABRT_CLR_MSK    0xffffffbf
/* The reset value of the ALT_I2C_RAW_INTR_STAT_TX_ABRT register field. */
#define ALT_I2C_RAW_INTR_STAT_TX_ABRT_RESET      0x0
/* Extracts the ALT_I2C_RAW_INTR_STAT_TX_ABRT field value from a register. */
#define ALT_I2C_RAW_INTR_STAT_TX_ABRT_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_I2C_RAW_INTR_STAT_TX_ABRT register field value suitable for setting the register. */
#define ALT_I2C_RAW_INTR_STAT_TX_ABRT_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Raw Interrupt RX Done - rx_done
 * 
 * When the I2C is acting as a slave-transmitter, this bit is set to 1 if the
 * master does not acknowledge a transmitted byte. This occurs on the last byte of
 * the transmission, indicating that the transmission is done.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_RAW_INTR_STAT_RX_DONE register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_DONE_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_I2C_RAW_INTR_STAT_RX_DONE register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_DONE_MSB        7
/* The width in bits of the ALT_I2C_RAW_INTR_STAT_RX_DONE register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_DONE_WIDTH      1
/* The mask used to set the ALT_I2C_RAW_INTR_STAT_RX_DONE register field value. */
#define ALT_I2C_RAW_INTR_STAT_RX_DONE_SET_MSK    0x00000080
/* The mask used to clear the ALT_I2C_RAW_INTR_STAT_RX_DONE register field value. */
#define ALT_I2C_RAW_INTR_STAT_RX_DONE_CLR_MSK    0xffffff7f
/* The reset value of the ALT_I2C_RAW_INTR_STAT_RX_DONE register field. */
#define ALT_I2C_RAW_INTR_STAT_RX_DONE_RESET      0x0
/* Extracts the ALT_I2C_RAW_INTR_STAT_RX_DONE field value from a register. */
#define ALT_I2C_RAW_INTR_STAT_RX_DONE_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_I2C_RAW_INTR_STAT_RX_DONE register field value suitable for setting the register. */
#define ALT_I2C_RAW_INTR_STAT_RX_DONE_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Raw Interrupt Activity - activity
 * 
 * This bit captures i2c activity and stays set until it is cleared. There are four
 * ways to clear it:
 * 
 * * Disabling the I2C
 * 
 * * Reading the ic_clr_activity register
 * 
 * * Reading the ic_clr_intr register
 * 
 * * System reset
 * 
 * Once this bit is set, it stays set unless one of the four methods is used to
 * clear it. Even if the i2c module is idle, this bit remains set until cleared,
 * indicating that there was activity on the bus.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_RAW_INTR_STAT_ACTIVITY register field. */
#define ALT_I2C_RAW_INTR_STAT_ACTIVITY_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_I2C_RAW_INTR_STAT_ACTIVITY register field. */
#define ALT_I2C_RAW_INTR_STAT_ACTIVITY_MSB        8
/* The width in bits of the ALT_I2C_RAW_INTR_STAT_ACTIVITY register field. */
#define ALT_I2C_RAW_INTR_STAT_ACTIVITY_WIDTH      1
/* The mask used to set the ALT_I2C_RAW_INTR_STAT_ACTIVITY register field value. */
#define ALT_I2C_RAW_INTR_STAT_ACTIVITY_SET_MSK    0x00000100
/* The mask used to clear the ALT_I2C_RAW_INTR_STAT_ACTIVITY register field value. */
#define ALT_I2C_RAW_INTR_STAT_ACTIVITY_CLR_MSK    0xfffffeff
/* The reset value of the ALT_I2C_RAW_INTR_STAT_ACTIVITY register field. */
#define ALT_I2C_RAW_INTR_STAT_ACTIVITY_RESET      0x0
/* Extracts the ALT_I2C_RAW_INTR_STAT_ACTIVITY field value from a register. */
#define ALT_I2C_RAW_INTR_STAT_ACTIVITY_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_I2C_RAW_INTR_STAT_ACTIVITY register field value suitable for setting the register. */
#define ALT_I2C_RAW_INTR_STAT_ACTIVITY_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Raw Interrupt Stop Detect - stop_det
 * 
 * Indicates whether a STOP condition has occurred on the I2C interface regardless
 * of whether I2C is operating in slave or master mode.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_RAW_INTR_STAT_STOP_DET register field. */
#define ALT_I2C_RAW_INTR_STAT_STOP_DET_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_I2C_RAW_INTR_STAT_STOP_DET register field. */
#define ALT_I2C_RAW_INTR_STAT_STOP_DET_MSB        9
/* The width in bits of the ALT_I2C_RAW_INTR_STAT_STOP_DET register field. */
#define ALT_I2C_RAW_INTR_STAT_STOP_DET_WIDTH      1
/* The mask used to set the ALT_I2C_RAW_INTR_STAT_STOP_DET register field value. */
#define ALT_I2C_RAW_INTR_STAT_STOP_DET_SET_MSK    0x00000200
/* The mask used to clear the ALT_I2C_RAW_INTR_STAT_STOP_DET register field value. */
#define ALT_I2C_RAW_INTR_STAT_STOP_DET_CLR_MSK    0xfffffdff
/* The reset value of the ALT_I2C_RAW_INTR_STAT_STOP_DET register field. */
#define ALT_I2C_RAW_INTR_STAT_STOP_DET_RESET      0x0
/* Extracts the ALT_I2C_RAW_INTR_STAT_STOP_DET field value from a register. */
#define ALT_I2C_RAW_INTR_STAT_STOP_DET_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_I2C_RAW_INTR_STAT_STOP_DET register field value suitable for setting the register. */
#define ALT_I2C_RAW_INTR_STAT_STOP_DET_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Raw Interrupt Start Detect - start_det
 * 
 * Indicates whether a START or RESTART condition has occurred on the I2C interface
 * regardless of whether I2C is operating in slave or master mode.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_RAW_INTR_STAT_START_DET register field. */
#define ALT_I2C_RAW_INTR_STAT_START_DET_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_I2C_RAW_INTR_STAT_START_DET register field. */
#define ALT_I2C_RAW_INTR_STAT_START_DET_MSB        10
/* The width in bits of the ALT_I2C_RAW_INTR_STAT_START_DET register field. */
#define ALT_I2C_RAW_INTR_STAT_START_DET_WIDTH      1
/* The mask used to set the ALT_I2C_RAW_INTR_STAT_START_DET register field value. */
#define ALT_I2C_RAW_INTR_STAT_START_DET_SET_MSK    0x00000400
/* The mask used to clear the ALT_I2C_RAW_INTR_STAT_START_DET register field value. */
#define ALT_I2C_RAW_INTR_STAT_START_DET_CLR_MSK    0xfffffbff
/* The reset value of the ALT_I2C_RAW_INTR_STAT_START_DET register field. */
#define ALT_I2C_RAW_INTR_STAT_START_DET_RESET      0x0
/* Extracts the ALT_I2C_RAW_INTR_STAT_START_DET field value from a register. */
#define ALT_I2C_RAW_INTR_STAT_START_DET_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_I2C_RAW_INTR_STAT_START_DET register field value suitable for setting the register. */
#define ALT_I2C_RAW_INTR_STAT_START_DET_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Raw Interrupt General Call - gen_call
 * 
 * Set only when a General Call address is received and it is acknowledged. It
 * stays set until it is cleared either by disabling I2C or when the CPU reads bit
 * 0 of the ic_clr_gen_call register. I2C stores the received data in the Rx
 * buffer.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_RAW_INTR_STAT_GEN_CALL register field. */
#define ALT_I2C_RAW_INTR_STAT_GEN_CALL_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_I2C_RAW_INTR_STAT_GEN_CALL register field. */
#define ALT_I2C_RAW_INTR_STAT_GEN_CALL_MSB        11
/* The width in bits of the ALT_I2C_RAW_INTR_STAT_GEN_CALL register field. */
#define ALT_I2C_RAW_INTR_STAT_GEN_CALL_WIDTH      1
/* The mask used to set the ALT_I2C_RAW_INTR_STAT_GEN_CALL register field value. */
#define ALT_I2C_RAW_INTR_STAT_GEN_CALL_SET_MSK    0x00000800
/* The mask used to clear the ALT_I2C_RAW_INTR_STAT_GEN_CALL register field value. */
#define ALT_I2C_RAW_INTR_STAT_GEN_CALL_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_I2C_RAW_INTR_STAT_GEN_CALL register field. */
#define ALT_I2C_RAW_INTR_STAT_GEN_CALL_RESET      0x0
/* Extracts the ALT_I2C_RAW_INTR_STAT_GEN_CALL field value from a register. */
#define ALT_I2C_RAW_INTR_STAT_GEN_CALL_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_I2C_RAW_INTR_STAT_GEN_CALL register field value suitable for setting the register. */
#define ALT_I2C_RAW_INTR_STAT_GEN_CALL_SET(value) (((value) << 11) & 0x00000800)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_RAW_INTR_STAT.
 */
struct ALT_I2C_RAW_INTR_STAT_s
{
    const uint32_t  rx_under  :  1;  /* I2C Raw Interrupt RX Under */
    const uint32_t  rx_over   :  1;  /* Raw Interrupt RX Over */
    const uint32_t  rx_full   :  1;  /* Raw Interrupt RX Full */
    const uint32_t  tx_over   :  1;  /* Raw Interrupt TX Over */
    const uint32_t  tx_empty  :  1;  /* Raw Interrupt TX Empty */
    const uint32_t  rd_req    :  1;  /* Raw Interrupt Read Request */
    const uint32_t  tx_abrt   :  1;  /* Raw Interrupt TX Abort */
    const uint32_t  rx_done   :  1;  /* Raw Interrupt RX Done */
    const uint32_t  activity  :  1;  /* Raw Interrupt Activity */
    const uint32_t  stop_det  :  1;  /* Raw Interrupt Stop Detect */
    const uint32_t  start_det :  1;  /* Raw Interrupt Start Detect */
    const uint32_t  gen_call  :  1;  /* Raw Interrupt General Call */
    uint32_t                  : 20;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_RAW_INTR_STAT. */
typedef volatile struct ALT_I2C_RAW_INTR_STAT_s  ALT_I2C_RAW_INTR_STAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_RAW_INTR_STAT register from the beginning of the component. */
#define ALT_I2C_RAW_INTR_STAT_OFST        0x34
/* The address of the ALT_I2C_RAW_INTR_STAT register. */
#define ALT_I2C_RAW_INTR_STAT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_RAW_INTR_STAT_OFST))

/*
 * Register : Receive FIFO Threshold Register - ic_rx_tl
 * 
 * I2C Receive FIFO Threshold Register.
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
 * Field : Receive FIFO Threshold Level - rx_tl
 * 
 * Controls the level of entries (or above) that triggers the RX_FULL interrupt
 * (bit 2 in IC_RAW_INTR_STAT register). The valid range is 0-255, with the
 * additional restriction that hardware does not allow this value to be set to a
 * value larger than the depth of the buffer. If an attempt is made to do that, the
 * actual value set will be the maximum depth of the buffer. A value of 0 sets the
 * threshold for 1 entry, and a value of 255 sets the threshold for 256 entries.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_RX_TL_RX_TL register field. */
#define ALT_I2C_RX_TL_RX_TL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_RX_TL_RX_TL register field. */
#define ALT_I2C_RX_TL_RX_TL_MSB        7
/* The width in bits of the ALT_I2C_RX_TL_RX_TL register field. */
#define ALT_I2C_RX_TL_RX_TL_WIDTH      8
/* The mask used to set the ALT_I2C_RX_TL_RX_TL register field value. */
#define ALT_I2C_RX_TL_RX_TL_SET_MSK    0x000000ff
/* The mask used to clear the ALT_I2C_RX_TL_RX_TL register field value. */
#define ALT_I2C_RX_TL_RX_TL_CLR_MSK    0xffffff00
/* The reset value of the ALT_I2C_RX_TL_RX_TL register field. */
#define ALT_I2C_RX_TL_RX_TL_RESET      0x0
/* Extracts the ALT_I2C_RX_TL_RX_TL field value from a register. */
#define ALT_I2C_RX_TL_RX_TL_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_I2C_RX_TL_RX_TL register field value suitable for setting the register. */
#define ALT_I2C_RX_TL_RX_TL_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_RX_TL.
 */
struct ALT_I2C_RX_TL_s
{
    uint32_t  rx_tl :  8;  /* Receive FIFO Threshold Level */
    uint32_t        : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_RX_TL. */
typedef volatile struct ALT_I2C_RX_TL_s  ALT_I2C_RX_TL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_RX_TL register from the beginning of the component. */
#define ALT_I2C_RX_TL_OFST        0x38
/* The address of the ALT_I2C_RX_TL register. */
#define ALT_I2C_RX_TL_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_RX_TL_OFST))

/*
 * Register : Transmit FIFO Threshold Level Register - ic_tx_tl
 * 
 * Sets FIFO depth for Interrupt.
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
 * Field : Transmit FIFO Threshold Level - tx_tl
 * 
 * Controls the level of entries (or below) that trigger the TX_EMPTY interrupt
 * (bit 4 in ic_raw_intr_stat register). The valid range is 0-255, with the
 * additional restriction that it may not be set to value larger than the depth of
 * the buffer. If an attempt is made to do that, the actual value set will be the
 * maximum depth of the buffer. A value of 0 sets the threshold for 0 entries, and
 * a value of 255 sets the threshold for 255 entries.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_TL_TX_TL register field. */
#define ALT_I2C_TX_TL_TX_TL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_TL_TX_TL register field. */
#define ALT_I2C_TX_TL_TX_TL_MSB        7
/* The width in bits of the ALT_I2C_TX_TL_TX_TL register field. */
#define ALT_I2C_TX_TL_TX_TL_WIDTH      8
/* The mask used to set the ALT_I2C_TX_TL_TX_TL register field value. */
#define ALT_I2C_TX_TL_TX_TL_SET_MSK    0x000000ff
/* The mask used to clear the ALT_I2C_TX_TL_TX_TL register field value. */
#define ALT_I2C_TX_TL_TX_TL_CLR_MSK    0xffffff00
/* The reset value of the ALT_I2C_TX_TL_TX_TL register field. */
#define ALT_I2C_TX_TL_TX_TL_RESET      0x0
/* Extracts the ALT_I2C_TX_TL_TX_TL field value from a register. */
#define ALT_I2C_TX_TL_TX_TL_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_I2C_TX_TL_TX_TL register field value suitable for setting the register. */
#define ALT_I2C_TX_TL_TX_TL_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_TX_TL.
 */
struct ALT_I2C_TX_TL_s
{
    uint32_t  tx_tl :  8;  /* Transmit FIFO Threshold Level */
    uint32_t        : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_TX_TL. */
typedef volatile struct ALT_I2C_TX_TL_s  ALT_I2C_TX_TL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_TX_TL register from the beginning of the component. */
#define ALT_I2C_TX_TL_OFST        0x3c
/* The address of the ALT_I2C_TX_TL register. */
#define ALT_I2C_TX_TL_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_TX_TL_OFST))

/*
 * Register : Combined and Individual Interrupt Register - ic_clr_intr
 * 
 * Controls Interrupts
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                           
 * :-------|:-------|:------|:---------------------------------------
 *  [0]    | R      | 0x0   | Combined and Individual Interrupt Bits
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                           
 * 
 */
/*
 * Field : Combined and Individual Interrupt Bits - clr_intr
 * 
 * Read this register to clear the combined interrupt, all individual interrupts,
 * and the IC_TX_ABRT_SOURCE register. This bit does not clear hardware clearable
 * interrupts but software clearable interrupts. Refer to Bit 9 of the
 * ic_tx_abrt_source register for an exception to clearing ic_tx_abrt_source.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_CLR_INTR_CLR_INTR register field. */
#define ALT_I2C_CLR_INTR_CLR_INTR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_CLR_INTR_CLR_INTR register field. */
#define ALT_I2C_CLR_INTR_CLR_INTR_MSB        0
/* The width in bits of the ALT_I2C_CLR_INTR_CLR_INTR register field. */
#define ALT_I2C_CLR_INTR_CLR_INTR_WIDTH      1
/* The mask used to set the ALT_I2C_CLR_INTR_CLR_INTR register field value. */
#define ALT_I2C_CLR_INTR_CLR_INTR_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_CLR_INTR_CLR_INTR register field value. */
#define ALT_I2C_CLR_INTR_CLR_INTR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_CLR_INTR_CLR_INTR register field. */
#define ALT_I2C_CLR_INTR_CLR_INTR_RESET      0x0
/* Extracts the ALT_I2C_CLR_INTR_CLR_INTR field value from a register. */
#define ALT_I2C_CLR_INTR_CLR_INTR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_CLR_INTR_CLR_INTR register field value suitable for setting the register. */
#define ALT_I2C_CLR_INTR_CLR_INTR_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_CLR_INTR.
 */
struct ALT_I2C_CLR_INTR_s
{
    const uint32_t  clr_intr :  1;  /* Combined and Individual Interrupt Bits */
    uint32_t                 : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_CLR_INTR. */
typedef volatile struct ALT_I2C_CLR_INTR_s  ALT_I2C_CLR_INTR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_CLR_INTR register from the beginning of the component. */
#define ALT_I2C_CLR_INTR_OFST        0x40
/* The address of the ALT_I2C_CLR_INTR register. */
#define ALT_I2C_CLR_INTR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_CLR_INTR_OFST))

/*
 * Register : Rx Under Interrupt Register - ic_clr_rx_under
 * 
 * Rx Under Interrupt Bits.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                 
 * :-------|:-------|:------|:-----------------------------
 *  [0]    | R      | 0x0   | Clear Rx Under Interrupt Bit
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                 
 * 
 */
/*
 * Field : Clear Rx Under Interrupt Bit - clr_rx_under
 * 
 * Read this register to clear the RX_UNDER interrupt bit 0 of the ic_raw_intr_stat
 * register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER register field. */
#define ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER register field. */
#define ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER_MSB        0
/* The width in bits of the ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER register field. */
#define ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER_WIDTH      1
/* The mask used to set the ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER register field value. */
#define ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER register field value. */
#define ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER register field. */
#define ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER_RESET      0x0
/* Extracts the ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER field value from a register. */
#define ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER register field value suitable for setting the register. */
#define ALT_I2C_CLR_RX_UNDER_CLR_RX_UNDER_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_CLR_RX_UNDER.
 */
struct ALT_I2C_CLR_RX_UNDER_s
{
    const uint32_t  clr_rx_under :  1;  /* Clear Rx Under Interrupt Bit */
    uint32_t                     : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_CLR_RX_UNDER. */
typedef volatile struct ALT_I2C_CLR_RX_UNDER_s  ALT_I2C_CLR_RX_UNDER_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_CLR_RX_UNDER register from the beginning of the component. */
#define ALT_I2C_CLR_RX_UNDER_OFST        0x44
/* The address of the ALT_I2C_CLR_RX_UNDER register. */
#define ALT_I2C_CLR_RX_UNDER_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_CLR_RX_UNDER_OFST))

/*
 * Register : RX Over Interrupt Register - ic_clr_rx_over
 * 
 * Clears Rx over Interrupt Bit
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description          
 * :-------|:-------|:------|:----------------------
 *  [0]    | R      | 0x0   | RX Over Interrupt Bit
 *  [31:1] | ???    | 0x0   | *UNDEFINED*          
 * 
 */
/*
 * Field : RX Over Interrupt Bit - clr_rx_over
 * 
 * Read this register to clear the RX_OVER interrupt bit 1 of the ic_raw_intr_stat
 * register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_CLR_RX_OVER_CLR_RX_OVER register field. */
#define ALT_I2C_CLR_RX_OVER_CLR_RX_OVER_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_CLR_RX_OVER_CLR_RX_OVER register field. */
#define ALT_I2C_CLR_RX_OVER_CLR_RX_OVER_MSB        0
/* The width in bits of the ALT_I2C_CLR_RX_OVER_CLR_RX_OVER register field. */
#define ALT_I2C_CLR_RX_OVER_CLR_RX_OVER_WIDTH      1
/* The mask used to set the ALT_I2C_CLR_RX_OVER_CLR_RX_OVER register field value. */
#define ALT_I2C_CLR_RX_OVER_CLR_RX_OVER_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_CLR_RX_OVER_CLR_RX_OVER register field value. */
#define ALT_I2C_CLR_RX_OVER_CLR_RX_OVER_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_CLR_RX_OVER_CLR_RX_OVER register field. */
#define ALT_I2C_CLR_RX_OVER_CLR_RX_OVER_RESET      0x0
/* Extracts the ALT_I2C_CLR_RX_OVER_CLR_RX_OVER field value from a register. */
#define ALT_I2C_CLR_RX_OVER_CLR_RX_OVER_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_CLR_RX_OVER_CLR_RX_OVER register field value suitable for setting the register. */
#define ALT_I2C_CLR_RX_OVER_CLR_RX_OVER_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_CLR_RX_OVER.
 */
struct ALT_I2C_CLR_RX_OVER_s
{
    const uint32_t  clr_rx_over :  1;  /* RX Over Interrupt Bit */
    uint32_t                    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_CLR_RX_OVER. */
typedef volatile struct ALT_I2C_CLR_RX_OVER_s  ALT_I2C_CLR_RX_OVER_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_CLR_RX_OVER register from the beginning of the component. */
#define ALT_I2C_CLR_RX_OVER_OFST        0x48
/* The address of the ALT_I2C_CLR_RX_OVER register. */
#define ALT_I2C_CLR_RX_OVER_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_CLR_RX_OVER_OFST))

/*
 * Register : TX Over Interrupt Register - ic_clr_tx_over
 * 
 * Clears Over Interrupts
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description          
 * :-------|:-------|:------|:----------------------
 *  [0]    | R      | 0x0   | TX Over Interrupt Bit
 *  [31:1] | ???    | 0x0   | *UNDEFINED*          
 * 
 */
/*
 * Field : TX Over Interrupt Bit - clr_tx_over
 * 
 * Read this register to clear the TX_OVER interrupt (bit 3) of the
 * ic_raw_intr_stat register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_CLR_TX_OVER_CLR_TX_OVER register field. */
#define ALT_I2C_CLR_TX_OVER_CLR_TX_OVER_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_CLR_TX_OVER_CLR_TX_OVER register field. */
#define ALT_I2C_CLR_TX_OVER_CLR_TX_OVER_MSB        0
/* The width in bits of the ALT_I2C_CLR_TX_OVER_CLR_TX_OVER register field. */
#define ALT_I2C_CLR_TX_OVER_CLR_TX_OVER_WIDTH      1
/* The mask used to set the ALT_I2C_CLR_TX_OVER_CLR_TX_OVER register field value. */
#define ALT_I2C_CLR_TX_OVER_CLR_TX_OVER_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_CLR_TX_OVER_CLR_TX_OVER register field value. */
#define ALT_I2C_CLR_TX_OVER_CLR_TX_OVER_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_CLR_TX_OVER_CLR_TX_OVER register field. */
#define ALT_I2C_CLR_TX_OVER_CLR_TX_OVER_RESET      0x0
/* Extracts the ALT_I2C_CLR_TX_OVER_CLR_TX_OVER field value from a register. */
#define ALT_I2C_CLR_TX_OVER_CLR_TX_OVER_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_CLR_TX_OVER_CLR_TX_OVER register field value suitable for setting the register. */
#define ALT_I2C_CLR_TX_OVER_CLR_TX_OVER_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_CLR_TX_OVER.
 */
struct ALT_I2C_CLR_TX_OVER_s
{
    const uint32_t  clr_tx_over :  1;  /* TX Over Interrupt Bit */
    uint32_t                    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_CLR_TX_OVER. */
typedef volatile struct ALT_I2C_CLR_TX_OVER_s  ALT_I2C_CLR_TX_OVER_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_CLR_TX_OVER register from the beginning of the component. */
#define ALT_I2C_CLR_TX_OVER_OFST        0x4c
/* The address of the ALT_I2C_CLR_TX_OVER register. */
#define ALT_I2C_CLR_TX_OVER_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_CLR_TX_OVER_OFST))

/*
 * Register : Interrupt Read Request Register - ic_clr_rd_req
 * 
 * Clear RD_REQ Interrupt Register
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                        
 * :-------|:-------|:------|:------------------------------------
 *  [0]    | R      | 0x0   | Interrupt Register Read Request Bit
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : Interrupt Register Read Request Bit - clr_rd_req
 * 
 * Read this register to clear the RD_REQ interrupt (bit 5) of the ic_raw_intr_stat
 * register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_CLR_RD_REQ_CLR_RD_REQ register field. */
#define ALT_I2C_CLR_RD_REQ_CLR_RD_REQ_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_CLR_RD_REQ_CLR_RD_REQ register field. */
#define ALT_I2C_CLR_RD_REQ_CLR_RD_REQ_MSB        0
/* The width in bits of the ALT_I2C_CLR_RD_REQ_CLR_RD_REQ register field. */
#define ALT_I2C_CLR_RD_REQ_CLR_RD_REQ_WIDTH      1
/* The mask used to set the ALT_I2C_CLR_RD_REQ_CLR_RD_REQ register field value. */
#define ALT_I2C_CLR_RD_REQ_CLR_RD_REQ_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_CLR_RD_REQ_CLR_RD_REQ register field value. */
#define ALT_I2C_CLR_RD_REQ_CLR_RD_REQ_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_CLR_RD_REQ_CLR_RD_REQ register field. */
#define ALT_I2C_CLR_RD_REQ_CLR_RD_REQ_RESET      0x0
/* Extracts the ALT_I2C_CLR_RD_REQ_CLR_RD_REQ field value from a register. */
#define ALT_I2C_CLR_RD_REQ_CLR_RD_REQ_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_CLR_RD_REQ_CLR_RD_REQ register field value suitable for setting the register. */
#define ALT_I2C_CLR_RD_REQ_CLR_RD_REQ_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_CLR_RD_REQ.
 */
struct ALT_I2C_CLR_RD_REQ_s
{
    const uint32_t  clr_rd_req :  1;  /* Interrupt Register Read Request Bit */
    uint32_t                   : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_CLR_RD_REQ. */
typedef volatile struct ALT_I2C_CLR_RD_REQ_s  ALT_I2C_CLR_RD_REQ_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_CLR_RD_REQ register from the beginning of the component. */
#define ALT_I2C_CLR_RD_REQ_OFST        0x50
/* The address of the ALT_I2C_CLR_RD_REQ register. */
#define ALT_I2C_CLR_RD_REQ_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_CLR_RD_REQ_OFST))

/*
 * Register : Tx Abort Interrupt Register - ic_clr_tx_abrt
 * 
 * Clear TX_ABRT Interrupt
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description           
 * :-------|:-------|:------|:-----------------------
 *  [0]    | R      | 0x0   | Tx Abort Interrupt Bit
 *  [31:1] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : Tx Abort Interrupt Bit - clr_tx_abort
 * 
 * Read this register to clear the TX_ABRT interrupt (bit 6) of the
 * ic_raw_intr_stat register, and the ic_tx_abrt_source register. This also
 * releases the TX FIFO from the flushed/reset state, allowing more writes to the
 * TX FIFO. Refer to Bit 9 of the ic_tx_abrt_source register for an exception to
 * clearing ic_tx_abrt_source.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT register field. */
#define ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT register field. */
#define ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT_MSB        0
/* The width in bits of the ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT register field. */
#define ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT_WIDTH      1
/* The mask used to set the ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT register field value. */
#define ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT register field value. */
#define ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT register field. */
#define ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT_RESET      0x0
/* Extracts the ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT field value from a register. */
#define ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT register field value suitable for setting the register. */
#define ALT_I2C_CLR_TX_ABRT_CLR_TX_ABT_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_CLR_TX_ABRT.
 */
struct ALT_I2C_CLR_TX_ABRT_s
{
    const uint32_t  clr_tx_abort :  1;  /* Tx Abort Interrupt Bit */
    uint32_t                     : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_CLR_TX_ABRT. */
typedef volatile struct ALT_I2C_CLR_TX_ABRT_s  ALT_I2C_CLR_TX_ABRT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_CLR_TX_ABRT register from the beginning of the component. */
#define ALT_I2C_CLR_TX_ABRT_OFST        0x54
/* The address of the ALT_I2C_CLR_TX_ABRT register. */
#define ALT_I2C_CLR_TX_ABRT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_CLR_TX_ABRT_OFST))

/*
 * Register : Rx Done Interrupt Register - ic_clr_rx_done
 * 
 * Clear RX_DONE Interrupt Register
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description          
 * :-------|:-------|:------|:----------------------
 *  [0]    | R      | 0x0   | RX_DONE Interrupt Bit
 *  [31:1] | ???    | 0x0   | *UNDEFINED*          
 * 
 */
/*
 * Field : RX_DONE Interrupt Bit - clr_rx_done
 * 
 * Read this register to clear the RX_DONE interrupt (bit 7) of the
 * ic_raw_intr_stat register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_CLR_RX_DONE_CLR_RX_DONE register field. */
#define ALT_I2C_CLR_RX_DONE_CLR_RX_DONE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_CLR_RX_DONE_CLR_RX_DONE register field. */
#define ALT_I2C_CLR_RX_DONE_CLR_RX_DONE_MSB        0
/* The width in bits of the ALT_I2C_CLR_RX_DONE_CLR_RX_DONE register field. */
#define ALT_I2C_CLR_RX_DONE_CLR_RX_DONE_WIDTH      1
/* The mask used to set the ALT_I2C_CLR_RX_DONE_CLR_RX_DONE register field value. */
#define ALT_I2C_CLR_RX_DONE_CLR_RX_DONE_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_CLR_RX_DONE_CLR_RX_DONE register field value. */
#define ALT_I2C_CLR_RX_DONE_CLR_RX_DONE_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_CLR_RX_DONE_CLR_RX_DONE register field. */
#define ALT_I2C_CLR_RX_DONE_CLR_RX_DONE_RESET      0x0
/* Extracts the ALT_I2C_CLR_RX_DONE_CLR_RX_DONE field value from a register. */
#define ALT_I2C_CLR_RX_DONE_CLR_RX_DONE_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_CLR_RX_DONE_CLR_RX_DONE register field value suitable for setting the register. */
#define ALT_I2C_CLR_RX_DONE_CLR_RX_DONE_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_CLR_RX_DONE.
 */
struct ALT_I2C_CLR_RX_DONE_s
{
    const uint32_t  clr_rx_done :  1;  /* RX_DONE Interrupt Bit */
    uint32_t                    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_CLR_RX_DONE. */
typedef volatile struct ALT_I2C_CLR_RX_DONE_s  ALT_I2C_CLR_RX_DONE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_CLR_RX_DONE register from the beginning of the component. */
#define ALT_I2C_CLR_RX_DONE_OFST        0x58
/* The address of the ALT_I2C_CLR_RX_DONE register. */
#define ALT_I2C_CLR_RX_DONE_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_CLR_RX_DONE_OFST))

/*
 * Register : Activity Interrupt Register - ic_clr_activity
 * 
 * Clears ACTIVITY Interrupt
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description           
 * :-------|:-------|:------|:-----------------------
 *  [0]    | R      | 0x0   | Activity Interrupt Bit
 *  [31:1] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : Activity Interrupt Bit - clr_activity
 * 
 * Reading this register clears the ACTIVITY interrupt if the I2C is not active
 * anymore. If the I2C module is still active on the bus, the ACTIVITY interrupt
 * bit continues to be set. It is automatically cleared by hardware if the module
 * is disabled and if there is no further activity on the bus. The value read from
 * this register to get status of the ACTIVITY interrupt (bit 8) of the
 * ic_raw_intr_stat register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY register field. */
#define ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY register field. */
#define ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY_MSB        0
/* The width in bits of the ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY register field. */
#define ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY_WIDTH      1
/* The mask used to set the ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY register field value. */
#define ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY register field value. */
#define ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY register field. */
#define ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY_RESET      0x0
/* Extracts the ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY field value from a register. */
#define ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY register field value suitable for setting the register. */
#define ALT_I2C_CLR_ACTIVITY_CLR_ACTIVITY_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_CLR_ACTIVITY.
 */
struct ALT_I2C_CLR_ACTIVITY_s
{
    const uint32_t  clr_activity :  1;  /* Activity Interrupt Bit */
    uint32_t                     : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_CLR_ACTIVITY. */
typedef volatile struct ALT_I2C_CLR_ACTIVITY_s  ALT_I2C_CLR_ACTIVITY_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_CLR_ACTIVITY register from the beginning of the component. */
#define ALT_I2C_CLR_ACTIVITY_OFST        0x5c
/* The address of the ALT_I2C_CLR_ACTIVITY register. */
#define ALT_I2C_CLR_ACTIVITY_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_CLR_ACTIVITY_OFST))

/*
 * Register : Stop Detect Interrupt Register - ic_clr_stop_det
 * 
 * Clear Interrupts.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description              
 * :-------|:-------|:------|:--------------------------
 *  [0]    | R      | 0x0   | Stop Detect Interrupt Bit
 *  [31:1] | ???    | 0x0   | *UNDEFINED*              
 * 
 */
/*
 * Field : Stop Detect Interrupt Bit - clr_stop_det
 * 
 * Read this register to clear the clr_stop_det interrupt (bit 9) of the
 * ic_raw_intr_stat register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_CLR_STOP_DET_CLR_STOP_DET register field. */
#define ALT_I2C_CLR_STOP_DET_CLR_STOP_DET_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_CLR_STOP_DET_CLR_STOP_DET register field. */
#define ALT_I2C_CLR_STOP_DET_CLR_STOP_DET_MSB        0
/* The width in bits of the ALT_I2C_CLR_STOP_DET_CLR_STOP_DET register field. */
#define ALT_I2C_CLR_STOP_DET_CLR_STOP_DET_WIDTH      1
/* The mask used to set the ALT_I2C_CLR_STOP_DET_CLR_STOP_DET register field value. */
#define ALT_I2C_CLR_STOP_DET_CLR_STOP_DET_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_CLR_STOP_DET_CLR_STOP_DET register field value. */
#define ALT_I2C_CLR_STOP_DET_CLR_STOP_DET_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_CLR_STOP_DET_CLR_STOP_DET register field. */
#define ALT_I2C_CLR_STOP_DET_CLR_STOP_DET_RESET      0x0
/* Extracts the ALT_I2C_CLR_STOP_DET_CLR_STOP_DET field value from a register. */
#define ALT_I2C_CLR_STOP_DET_CLR_STOP_DET_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_CLR_STOP_DET_CLR_STOP_DET register field value suitable for setting the register. */
#define ALT_I2C_CLR_STOP_DET_CLR_STOP_DET_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_CLR_STOP_DET.
 */
struct ALT_I2C_CLR_STOP_DET_s
{
    const uint32_t  clr_stop_det :  1;  /* Stop Detect Interrupt Bit */
    uint32_t                     : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_CLR_STOP_DET. */
typedef volatile struct ALT_I2C_CLR_STOP_DET_s  ALT_I2C_CLR_STOP_DET_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_CLR_STOP_DET register from the beginning of the component. */
#define ALT_I2C_CLR_STOP_DET_OFST        0x60
/* The address of the ALT_I2C_CLR_STOP_DET register. */
#define ALT_I2C_CLR_STOP_DET_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_CLR_STOP_DET_OFST))

/*
 * Register : Start Detect Interrupt Register - ic_clr_start_det
 * 
 * Clears START_DET Interrupt
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description               
 * :-------|:-------|:------|:---------------------------
 *  [0]    | R      | 0x0   | Start Detect Interrupt Bit
 *  [31:1] | ???    | 0x0   | *UNDEFINED*               
 * 
 */
/*
 * Field : Start Detect Interrupt Bit - clr_start_det
 * 
 * Read this register to clear the start_det interrupt (bit 10) of the
 * ic_raw_intr_stat register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_CLR_START_DET_CLR_START_DET register field. */
#define ALT_I2C_CLR_START_DET_CLR_START_DET_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_CLR_START_DET_CLR_START_DET register field. */
#define ALT_I2C_CLR_START_DET_CLR_START_DET_MSB        0
/* The width in bits of the ALT_I2C_CLR_START_DET_CLR_START_DET register field. */
#define ALT_I2C_CLR_START_DET_CLR_START_DET_WIDTH      1
/* The mask used to set the ALT_I2C_CLR_START_DET_CLR_START_DET register field value. */
#define ALT_I2C_CLR_START_DET_CLR_START_DET_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_CLR_START_DET_CLR_START_DET register field value. */
#define ALT_I2C_CLR_START_DET_CLR_START_DET_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_CLR_START_DET_CLR_START_DET register field. */
#define ALT_I2C_CLR_START_DET_CLR_START_DET_RESET      0x0
/* Extracts the ALT_I2C_CLR_START_DET_CLR_START_DET field value from a register. */
#define ALT_I2C_CLR_START_DET_CLR_START_DET_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_CLR_START_DET_CLR_START_DET register field value suitable for setting the register. */
#define ALT_I2C_CLR_START_DET_CLR_START_DET_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_CLR_START_DET.
 */
struct ALT_I2C_CLR_START_DET_s
{
    const uint32_t  clr_start_det :  1;  /* Start Detect Interrupt Bit */
    uint32_t                      : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_CLR_START_DET. */
typedef volatile struct ALT_I2C_CLR_START_DET_s  ALT_I2C_CLR_START_DET_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_CLR_START_DET register from the beginning of the component. */
#define ALT_I2C_CLR_START_DET_OFST        0x64
/* The address of the ALT_I2C_CLR_START_DET register. */
#define ALT_I2C_CLR_START_DET_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_CLR_START_DET_OFST))

/*
 * Register : GEN CALL Interrupt Register - ic_clr_gen_call
 * 
 * Clear GEN_CALL Interrupt Register
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description           
 * :-------|:-------|:------|:-----------------------
 *  [0]    | R      | 0x0   | GEN CALL Interrupt Bit
 *  [31:1] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : GEN CALL Interrupt Bit - clr_gen_call
 * 
 * Read this register to clear the GEN_CALL interrupt (bit 11) of ic_raw_intr_stat
 * register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL register field. */
#define ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL register field. */
#define ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL_MSB        0
/* The width in bits of the ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL register field. */
#define ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL_WIDTH      1
/* The mask used to set the ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL register field value. */
#define ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL register field value. */
#define ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL register field. */
#define ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL_RESET      0x0
/* Extracts the ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL field value from a register. */
#define ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL register field value suitable for setting the register. */
#define ALT_I2C_CLR_GEN_CALL_CLR_GEN_CALL_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_CLR_GEN_CALL.
 */
struct ALT_I2C_CLR_GEN_CALL_s
{
    const uint32_t  clr_gen_call :  1;  /* GEN CALL Interrupt Bit */
    uint32_t                     : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_CLR_GEN_CALL. */
typedef volatile struct ALT_I2C_CLR_GEN_CALL_s  ALT_I2C_CLR_GEN_CALL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_CLR_GEN_CALL register from the beginning of the component. */
#define ALT_I2C_CLR_GEN_CALL_OFST        0x68
/* The address of the ALT_I2C_CLR_GEN_CALL register. */
#define ALT_I2C_CLR_GEN_CALL_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_CLR_GEN_CALL_OFST))

/*
 * Register : Enable Register - ic_enable
 * 
 * Enable and disable i2c operation
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description 
 * :-------|:-------|:------|:-------------
 *  [0]    | RW     | 0x0   | Enable Bit  
 *  [1]    | RW     | 0x0   | TX abort Bit
 *  [31:2] | ???    | 0x0   | *UNDEFINED* 
 * 
 */
/*
 * Field : Enable Bit - enable
 * 
 * Controls whether the I2C is enabled. Software can disable I2C while it is
 * active. However, it is important that care be taken to ensure that I2C is
 * disabled properly. When the I2C is disabled, the following occurs:
 * 
 * The TX FIFO and RX FIFO get flushed. Status bits in the IC_INTR_STAT register
 * are still active until I2C goes into IDLE state. If the module is transmitting,
 * it stops as well as deletes the contents of the transmit buffer after the
 * current transfer is complete. If the module is receiving, the I2C stops the
 * current transfer at the end of the current byte and does not acknowledge the
 * transfer. The l4_sp_clk synchronizes pclk and ic_clk. The register
 * ic_enable_status is added to allow software to determine when the hardware has
 * completely shutdown in response to the IC_ENABLE register being set from 1 to 0.
 * Only one register is required to be monitored. Procedure for Disabling I2C
 * 
 * 1. Define a timer interval (ti2c_poll) equal to the 10 times the signaling
 * period for the highest I2C transfer speed used in the system and supported by
 * I2C. For example, if the highest I2C transfer mode is 400 kb/s, then this
 * ti2c_poll is 25us.
 * 
 * 2. Define a maximum time-out parameter, MAX_T_POLL_COUNT, such that if any
 * repeated polling operation exceeds this maximum value, an error is reported. 3.
 * Execute a blocking thread/process/function that prevents any further I2C master
 * transactions to be started by software, but allows any pending transfers to be
 * completed.
 * 
 * 4. The variable POLL_COUNT is initialized to zero. 5. Set IC_ENABLE to 0.
 * 
 * 6. Read the IC_ENABLE_STATUS register and test the IC_EN bit (bit 0). Increment
 * POLL_COUNT by one. If POLL_COUNT >= MAX_T_POLL_COUNT, exit with the relevant
 * error code.
 * 
 * 7. If IC_ENABLE_STATUS[0] is 1, then sleep for ti2c_poll and proceed to the
 * previous step. Otherwise, exit with a relevant success code.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                | Value | Description                                   
 * :--------------------|:------|:-----------------------------------------------
 *  ALT_I2C_EN_EN_E_DIS | 0x0   | Disables i2c. TX and RX FIFOs are held in an  
 * :                    |       | erased state                                  
 *  ALT_I2C_EN_EN_E_EN  | 0x1   | Enables i2c. Software can disable i2c while it
 * :                    |       | is active                                     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_EN_EN
 * 
 * Disables i2c. TX and RX FIFOs are held in an erased state
 */
#define ALT_I2C_EN_EN_E_DIS 0x0
/*
 * Enumerated value for register field ALT_I2C_EN_EN
 * 
 * Enables i2c. Software can disable i2c while it is active
 */
#define ALT_I2C_EN_EN_E_EN  0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_EN_EN register field. */
#define ALT_I2C_EN_EN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_EN_EN register field. */
#define ALT_I2C_EN_EN_MSB        0
/* The width in bits of the ALT_I2C_EN_EN register field. */
#define ALT_I2C_EN_EN_WIDTH      1
/* The mask used to set the ALT_I2C_EN_EN register field value. */
#define ALT_I2C_EN_EN_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_EN_EN register field value. */
#define ALT_I2C_EN_EN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_EN_EN register field. */
#define ALT_I2C_EN_EN_RESET      0x0
/* Extracts the ALT_I2C_EN_EN field value from a register. */
#define ALT_I2C_EN_EN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_EN_EN register field value suitable for setting the register. */
#define ALT_I2C_EN_EN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : TX abort Bit - txabort
 * 
 * Write 1 does a TX abort. Self cleared on abort completion
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_EN_TXABT register field. */
#define ALT_I2C_EN_TXABT_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_I2C_EN_TXABT register field. */
#define ALT_I2C_EN_TXABT_MSB        1
/* The width in bits of the ALT_I2C_EN_TXABT register field. */
#define ALT_I2C_EN_TXABT_WIDTH      1
/* The mask used to set the ALT_I2C_EN_TXABT register field value. */
#define ALT_I2C_EN_TXABT_SET_MSK    0x00000002
/* The mask used to clear the ALT_I2C_EN_TXABT register field value. */
#define ALT_I2C_EN_TXABT_CLR_MSK    0xfffffffd
/* The reset value of the ALT_I2C_EN_TXABT register field. */
#define ALT_I2C_EN_TXABT_RESET      0x0
/* Extracts the ALT_I2C_EN_TXABT field value from a register. */
#define ALT_I2C_EN_TXABT_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_I2C_EN_TXABT register field value suitable for setting the register. */
#define ALT_I2C_EN_TXABT_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_EN.
 */
struct ALT_I2C_EN_s
{
    uint32_t  enable  :  1;  /* Enable Bit */
    uint32_t  txabort :  1;  /* TX abort Bit */
    uint32_t          : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_EN. */
typedef volatile struct ALT_I2C_EN_s  ALT_I2C_EN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_EN register from the beginning of the component. */
#define ALT_I2C_EN_OFST        0x6c
/* The address of the ALT_I2C_EN register. */
#define ALT_I2C_EN_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_EN_OFST))

/*
 * Register : Status Register - ic_status
 * 
 * This is a read-only register used to indicate the current transfer status and
 * FIFO status. The status register may be read at any time. None of the bits in
 * this register request an interrupt.When the I2C is disabled by writing 0 in bit
 * 0 of the ic_enable register:
 * 
 * * Bits 1 and 2 are set to 1
 * 
 * * Bits 3 and 4 are set to 0
 * 
 * When the master or slave state machines goes to idle
 * 
 * * Bits 5 and 6 are set to 0
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                   
 * :-------|:-------|:------|:-------------------------------
 *  [0]    | R      | 0x0   | Activity Status Bit           
 *  [1]    | R      | 0x1   | TX FIFO Not Full Bit          
 *  [2]    | R      | 0x1   | TX FIFO Empty Bit             
 *  [3]    | R      | 0x0   | RX FIFO Empty Bit             
 *  [4]    | R      | 0x0   | RX FIFO Full Bit              
 *  [5]    | R      | 0x0   | Master FSM Activity Status Bit
 *  [6]    | R      | 0x0   | Slave FSM Activity Status Bit 
 *  [31:7] | ???    | 0x0   | *UNDEFINED*                   
 * 
 */
/*
 * Field : Activity Status Bit - activity
 * 
 * I2C Activity.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_STAT_ACTIVITY register field. */
#define ALT_I2C_STAT_ACTIVITY_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_STAT_ACTIVITY register field. */
#define ALT_I2C_STAT_ACTIVITY_MSB        0
/* The width in bits of the ALT_I2C_STAT_ACTIVITY register field. */
#define ALT_I2C_STAT_ACTIVITY_WIDTH      1
/* The mask used to set the ALT_I2C_STAT_ACTIVITY register field value. */
#define ALT_I2C_STAT_ACTIVITY_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_STAT_ACTIVITY register field value. */
#define ALT_I2C_STAT_ACTIVITY_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_STAT_ACTIVITY register field. */
#define ALT_I2C_STAT_ACTIVITY_RESET      0x0
/* Extracts the ALT_I2C_STAT_ACTIVITY field value from a register. */
#define ALT_I2C_STAT_ACTIVITY_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_STAT_ACTIVITY register field value suitable for setting the register. */
#define ALT_I2C_STAT_ACTIVITY_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : TX FIFO Not Full Bit - tfnf
 * 
 * Transmit Fifo Full
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description              
 * :----------------------------|:------|:--------------------------
 *  ALT_I2C_STAT_TFNF_E_FULL    | 0x0   | Transmit FIFO is full    
 *  ALT_I2C_STAT_TFNF_E_NOTFULL | 0x1   | Transmit FIFO is not full
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_STAT_TFNF
 * 
 * Transmit FIFO is full
 */
#define ALT_I2C_STAT_TFNF_E_FULL    0x0
/*
 * Enumerated value for register field ALT_I2C_STAT_TFNF
 * 
 * Transmit FIFO is not full
 */
#define ALT_I2C_STAT_TFNF_E_NOTFULL 0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_STAT_TFNF register field. */
#define ALT_I2C_STAT_TFNF_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_I2C_STAT_TFNF register field. */
#define ALT_I2C_STAT_TFNF_MSB        1
/* The width in bits of the ALT_I2C_STAT_TFNF register field. */
#define ALT_I2C_STAT_TFNF_WIDTH      1
/* The mask used to set the ALT_I2C_STAT_TFNF register field value. */
#define ALT_I2C_STAT_TFNF_SET_MSK    0x00000002
/* The mask used to clear the ALT_I2C_STAT_TFNF register field value. */
#define ALT_I2C_STAT_TFNF_CLR_MSK    0xfffffffd
/* The reset value of the ALT_I2C_STAT_TFNF register field. */
#define ALT_I2C_STAT_TFNF_RESET      0x1
/* Extracts the ALT_I2C_STAT_TFNF field value from a register. */
#define ALT_I2C_STAT_TFNF_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_I2C_STAT_TFNF register field value suitable for setting the register. */
#define ALT_I2C_STAT_TFNF_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : TX FIFO Empty Bit - tfe
 * 
 * Transmit FIFO Empty.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description               
 * :----------------------------|:------|:---------------------------
 *  ALT_I2C_STAT_TFE_E_NOTEMPTY | 0x0   | Transmit FIFO is not empty
 *  ALT_I2C_STAT_TFE_E_EMPTY    | 0x1   | Transmit FIFO is empty    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_STAT_TFE
 * 
 * Transmit FIFO is not empty
 */
#define ALT_I2C_STAT_TFE_E_NOTEMPTY 0x0
/*
 * Enumerated value for register field ALT_I2C_STAT_TFE
 * 
 * Transmit FIFO is empty
 */
#define ALT_I2C_STAT_TFE_E_EMPTY    0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_STAT_TFE register field. */
#define ALT_I2C_STAT_TFE_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_I2C_STAT_TFE register field. */
#define ALT_I2C_STAT_TFE_MSB        2
/* The width in bits of the ALT_I2C_STAT_TFE register field. */
#define ALT_I2C_STAT_TFE_WIDTH      1
/* The mask used to set the ALT_I2C_STAT_TFE register field value. */
#define ALT_I2C_STAT_TFE_SET_MSK    0x00000004
/* The mask used to clear the ALT_I2C_STAT_TFE register field value. */
#define ALT_I2C_STAT_TFE_CLR_MSK    0xfffffffb
/* The reset value of the ALT_I2C_STAT_TFE register field. */
#define ALT_I2C_STAT_TFE_RESET      0x1
/* Extracts the ALT_I2C_STAT_TFE field value from a register. */
#define ALT_I2C_STAT_TFE_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_I2C_STAT_TFE register field value suitable for setting the register. */
#define ALT_I2C_STAT_TFE_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : RX FIFO Empty Bit - rfne
 * 
 * Receive FIFO Not Empty.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description              
 * :-----------------------------|:------|:--------------------------
 *  ALT_I2C_STAT_RFNE_E_EMPTY    | 0x0   | Receive FIFO is empty    
 *  ALT_I2C_STAT_RFNE_E_NOTEMPTY | 0x1   | Receive FIFO is not empty
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_STAT_RFNE
 * 
 * Receive FIFO is empty
 */
#define ALT_I2C_STAT_RFNE_E_EMPTY       0x0
/*
 * Enumerated value for register field ALT_I2C_STAT_RFNE
 * 
 * Receive FIFO is not empty
 */
#define ALT_I2C_STAT_RFNE_E_NOTEMPTY    0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_STAT_RFNE register field. */
#define ALT_I2C_STAT_RFNE_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_I2C_STAT_RFNE register field. */
#define ALT_I2C_STAT_RFNE_MSB        3
/* The width in bits of the ALT_I2C_STAT_RFNE register field. */
#define ALT_I2C_STAT_RFNE_WIDTH      1
/* The mask used to set the ALT_I2C_STAT_RFNE register field value. */
#define ALT_I2C_STAT_RFNE_SET_MSK    0x00000008
/* The mask used to clear the ALT_I2C_STAT_RFNE register field value. */
#define ALT_I2C_STAT_RFNE_CLR_MSK    0xfffffff7
/* The reset value of the ALT_I2C_STAT_RFNE register field. */
#define ALT_I2C_STAT_RFNE_RESET      0x0
/* Extracts the ALT_I2C_STAT_RFNE field value from a register. */
#define ALT_I2C_STAT_RFNE_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_I2C_STAT_RFNE register field value suitable for setting the register. */
#define ALT_I2C_STAT_RFNE_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : RX FIFO Full Bit - rff
 * 
 * Receive FIFO Completely Full.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description             
 * :---------------------------|:------|:-------------------------
 *  ALT_I2C_STAT_RFF_E_NOTFULL | 0x0   | Receive FIFO is not full
 *  ALT_I2C_STAT_RFF_E_FULL    | 0x1   | Receive FIFO is full    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_STAT_RFF
 * 
 * Receive FIFO is not full
 */
#define ALT_I2C_STAT_RFF_E_NOTFULL  0x0
/*
 * Enumerated value for register field ALT_I2C_STAT_RFF
 * 
 * Receive FIFO is full
 */
#define ALT_I2C_STAT_RFF_E_FULL     0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_STAT_RFF register field. */
#define ALT_I2C_STAT_RFF_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_I2C_STAT_RFF register field. */
#define ALT_I2C_STAT_RFF_MSB        4
/* The width in bits of the ALT_I2C_STAT_RFF register field. */
#define ALT_I2C_STAT_RFF_WIDTH      1
/* The mask used to set the ALT_I2C_STAT_RFF register field value. */
#define ALT_I2C_STAT_RFF_SET_MSK    0x00000010
/* The mask used to clear the ALT_I2C_STAT_RFF register field value. */
#define ALT_I2C_STAT_RFF_CLR_MSK    0xffffffef
/* The reset value of the ALT_I2C_STAT_RFF register field. */
#define ALT_I2C_STAT_RFF_RESET      0x0
/* Extracts the ALT_I2C_STAT_RFF field value from a register. */
#define ALT_I2C_STAT_RFF_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_I2C_STAT_RFF register field value suitable for setting the register. */
#define ALT_I2C_STAT_RFF_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Master FSM Activity Status Bit - mst_activity
 * 
 * When the Master Finite State Machine (FSM) is not in the IDLE state, this bit is
 * set. Note:IC_STATUS[0]-that is, ACTIVITY bit-is the OR of SLV_ACTIVITY and
 * MST_ACTIVITY bits.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                                    
 * :------------------------------------|:------|:------------------------------------------------
 *  ALT_I2C_STAT_MST_ACTIVITY_E_IDLE    | 0x0   | Master FSM is in IDLE state. Master part of i2c
 * :                                    |       | is not Active                                  
 *  ALT_I2C_STAT_MST_ACTIVITY_E_NOTIDLE | 0x1   | Master FSM is not in IDLE state. Master part of
 * :                                    |       | i2c is Active                                  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_STAT_MST_ACTIVITY
 * 
 * Master FSM is in IDLE state. Master part of i2c is not Active
 */
#define ALT_I2C_STAT_MST_ACTIVITY_E_IDLE    0x0
/*
 * Enumerated value for register field ALT_I2C_STAT_MST_ACTIVITY
 * 
 * Master FSM is not in IDLE state. Master part of i2c is Active
 */
#define ALT_I2C_STAT_MST_ACTIVITY_E_NOTIDLE 0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_STAT_MST_ACTIVITY register field. */
#define ALT_I2C_STAT_MST_ACTIVITY_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_I2C_STAT_MST_ACTIVITY register field. */
#define ALT_I2C_STAT_MST_ACTIVITY_MSB        5
/* The width in bits of the ALT_I2C_STAT_MST_ACTIVITY register field. */
#define ALT_I2C_STAT_MST_ACTIVITY_WIDTH      1
/* The mask used to set the ALT_I2C_STAT_MST_ACTIVITY register field value. */
#define ALT_I2C_STAT_MST_ACTIVITY_SET_MSK    0x00000020
/* The mask used to clear the ALT_I2C_STAT_MST_ACTIVITY register field value. */
#define ALT_I2C_STAT_MST_ACTIVITY_CLR_MSK    0xffffffdf
/* The reset value of the ALT_I2C_STAT_MST_ACTIVITY register field. */
#define ALT_I2C_STAT_MST_ACTIVITY_RESET      0x0
/* Extracts the ALT_I2C_STAT_MST_ACTIVITY field value from a register. */
#define ALT_I2C_STAT_MST_ACTIVITY_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_I2C_STAT_MST_ACTIVITY register field value suitable for setting the register. */
#define ALT_I2C_STAT_MST_ACTIVITY_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Slave FSM Activity Status Bit - slv_activity
 * 
 * Slave FSM Activity Status. When the Slave Finite State Machine (FSM) is not in
 * the IDLE state, this bit is set.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                                     
 * :------------------------------------|:------|:-------------------------------------------------
 *  ALT_I2C_STAT_SLV_ACTIVITY_E_IDLE    | 0x0   | Slave FSM is in IDLE state so the Slave part of 
 * :                                    |       | i2c is not Active                               
 *  ALT_I2C_STAT_SLV_ACTIVITY_E_NOTIDLE | 0x1   | Slave FSM is not in IDLE state so the Slave part
 * :                                    |       | of i2c is Active                                
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_STAT_SLV_ACTIVITY
 * 
 * Slave FSM is in IDLE state so the Slave part of i2c is not Active
 */
#define ALT_I2C_STAT_SLV_ACTIVITY_E_IDLE    0x0
/*
 * Enumerated value for register field ALT_I2C_STAT_SLV_ACTIVITY
 * 
 * Slave FSM is not in IDLE state so the Slave part of i2c is Active
 */
#define ALT_I2C_STAT_SLV_ACTIVITY_E_NOTIDLE 0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_STAT_SLV_ACTIVITY register field. */
#define ALT_I2C_STAT_SLV_ACTIVITY_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_I2C_STAT_SLV_ACTIVITY register field. */
#define ALT_I2C_STAT_SLV_ACTIVITY_MSB        6
/* The width in bits of the ALT_I2C_STAT_SLV_ACTIVITY register field. */
#define ALT_I2C_STAT_SLV_ACTIVITY_WIDTH      1
/* The mask used to set the ALT_I2C_STAT_SLV_ACTIVITY register field value. */
#define ALT_I2C_STAT_SLV_ACTIVITY_SET_MSK    0x00000040
/* The mask used to clear the ALT_I2C_STAT_SLV_ACTIVITY register field value. */
#define ALT_I2C_STAT_SLV_ACTIVITY_CLR_MSK    0xffffffbf
/* The reset value of the ALT_I2C_STAT_SLV_ACTIVITY register field. */
#define ALT_I2C_STAT_SLV_ACTIVITY_RESET      0x0
/* Extracts the ALT_I2C_STAT_SLV_ACTIVITY field value from a register. */
#define ALT_I2C_STAT_SLV_ACTIVITY_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_I2C_STAT_SLV_ACTIVITY register field value suitable for setting the register. */
#define ALT_I2C_STAT_SLV_ACTIVITY_SET(value) (((value) << 6) & 0x00000040)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_STAT.
 */
struct ALT_I2C_STAT_s
{
    const uint32_t  activity     :  1;  /* Activity Status Bit */
    const uint32_t  tfnf         :  1;  /* TX FIFO Not Full Bit */
    const uint32_t  tfe          :  1;  /* TX FIFO Empty Bit */
    const uint32_t  rfne         :  1;  /* RX FIFO Empty Bit */
    const uint32_t  rff          :  1;  /* RX FIFO Full Bit */
    const uint32_t  mst_activity :  1;  /* Master FSM Activity Status Bit */
    const uint32_t  slv_activity :  1;  /* Slave FSM Activity Status Bit */
    uint32_t                     : 25;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_STAT. */
typedef volatile struct ALT_I2C_STAT_s  ALT_I2C_STAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_STAT register from the beginning of the component. */
#define ALT_I2C_STAT_OFST        0x70
/* The address of the ALT_I2C_STAT register. */
#define ALT_I2C_STAT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_STAT_OFST))

/*
 * Register : Transmit FIFO Level Register - ic_txflr
 * 
 * This register contains the number of valid data entries in the transmit FIFO
 * buffer. It is cleared whenever:
 * 
 * * The I2C is disabled
 * 
 * * There is a transmit abort that is, TX_ABRT bit is set in the ic_raw_intr_stat
 *   register. The slave bulk transmit mode is aborted The register increments
 *   whenever data is placed into the transmit FIFO and decrements when data is
 *   taken from the transmit FIFO.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description            
 * :-------|:-------|:------|:------------------------
 *  [6:0]  | R      | 0x0   | Transmit FIFO Level Bit
 *  [31:7] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : Transmit FIFO Level Bit - txflr
 * 
 * Transmit FIFO Level.Contains the number of valid data entries in the transmit
 * FIFO.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TXFLR_TXFLR register field. */
#define ALT_I2C_TXFLR_TXFLR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_TXFLR_TXFLR register field. */
#define ALT_I2C_TXFLR_TXFLR_MSB        6
/* The width in bits of the ALT_I2C_TXFLR_TXFLR register field. */
#define ALT_I2C_TXFLR_TXFLR_WIDTH      7
/* The mask used to set the ALT_I2C_TXFLR_TXFLR register field value. */
#define ALT_I2C_TXFLR_TXFLR_SET_MSK    0x0000007f
/* The mask used to clear the ALT_I2C_TXFLR_TXFLR register field value. */
#define ALT_I2C_TXFLR_TXFLR_CLR_MSK    0xffffff80
/* The reset value of the ALT_I2C_TXFLR_TXFLR register field. */
#define ALT_I2C_TXFLR_TXFLR_RESET      0x0
/* Extracts the ALT_I2C_TXFLR_TXFLR field value from a register. */
#define ALT_I2C_TXFLR_TXFLR_GET(value) (((value) & 0x0000007f) >> 0)
/* Produces a ALT_I2C_TXFLR_TXFLR register field value suitable for setting the register. */
#define ALT_I2C_TXFLR_TXFLR_SET(value) (((value) << 0) & 0x0000007f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_TXFLR.
 */
struct ALT_I2C_TXFLR_s
{
    const uint32_t  txflr :  7;  /* Transmit FIFO Level Bit */
    uint32_t              : 25;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_TXFLR. */
typedef volatile struct ALT_I2C_TXFLR_s  ALT_I2C_TXFLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_TXFLR register from the beginning of the component. */
#define ALT_I2C_TXFLR_OFST        0x74
/* The address of the ALT_I2C_TXFLR register. */
#define ALT_I2C_TXFLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_TXFLR_OFST))

/*
 * Register : Receive FIFO Level Register - ic_rxflr
 * 
 * This register contains the number of valid data entries in the receive FIFO
 * buffer. It is cleared whenever:
 * 
 * * The I2C is disabled
 * 
 * * Whenever there is a transmit abort caused by any of the events tracked in
 *   ic_tx_abrt_source The register increments whenever data is placed into the
 *   receive FIFO and decrements when data is taken from the receive FIFO.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description           
 * :-------|:-------|:------|:-----------------------
 *  [6:0]  | R      | 0x0   | Receive FIFO Level Bit
 *  [31:7] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : Receive FIFO Level Bit - rxflr
 * 
 * Receive FIFO Level. Contains the number of valid data entries in the receive
 * FIFO.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_RXFLR_RXFLR register field. */
#define ALT_I2C_RXFLR_RXFLR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_RXFLR_RXFLR register field. */
#define ALT_I2C_RXFLR_RXFLR_MSB        6
/* The width in bits of the ALT_I2C_RXFLR_RXFLR register field. */
#define ALT_I2C_RXFLR_RXFLR_WIDTH      7
/* The mask used to set the ALT_I2C_RXFLR_RXFLR register field value. */
#define ALT_I2C_RXFLR_RXFLR_SET_MSK    0x0000007f
/* The mask used to clear the ALT_I2C_RXFLR_RXFLR register field value. */
#define ALT_I2C_RXFLR_RXFLR_CLR_MSK    0xffffff80
/* The reset value of the ALT_I2C_RXFLR_RXFLR register field. */
#define ALT_I2C_RXFLR_RXFLR_RESET      0x0
/* Extracts the ALT_I2C_RXFLR_RXFLR field value from a register. */
#define ALT_I2C_RXFLR_RXFLR_GET(value) (((value) & 0x0000007f) >> 0)
/* Produces a ALT_I2C_RXFLR_RXFLR register field value suitable for setting the register. */
#define ALT_I2C_RXFLR_RXFLR_SET(value) (((value) << 0) & 0x0000007f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_RXFLR.
 */
struct ALT_I2C_RXFLR_s
{
    const uint32_t  rxflr :  7;  /* Receive FIFO Level Bit */
    uint32_t              : 25;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_RXFLR. */
typedef volatile struct ALT_I2C_RXFLR_s  ALT_I2C_RXFLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_RXFLR register from the beginning of the component. */
#define ALT_I2C_RXFLR_OFST        0x78
/* The address of the ALT_I2C_RXFLR register. */
#define ALT_I2C_RXFLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_RXFLR_OFST))

/*
 * Register : SDA Hold Register - ic_sda_hold
 * 
 * This register controls the amount of time delay (in terms of number of l4_sp_clk
 * clock periods) introduced in the falling edge of SCL, relative to SDA changing,
 * when I2C services a read request in a slave-transmitter operation.  The relevant
 * I2C requirement is thd:DAT as detailed in the I2C Bus Specification.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description 
 * :--------|:-------|:------|:-------------
 *  [15:0]  | RW     | 0x1   | SDA Hold Bit
 *  [31:16] | ???    | 0x0   | *UNDEFINED* 
 * 
 */
/*
 * Field : SDA Hold Bit - ic_sda_hold
 * 
 * Program to a minimum 0f 300ns.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_SDA_HOLD_IC_SDA_HOLD register field. */
#define ALT_I2C_SDA_HOLD_IC_SDA_HOLD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_SDA_HOLD_IC_SDA_HOLD register field. */
#define ALT_I2C_SDA_HOLD_IC_SDA_HOLD_MSB        15
/* The width in bits of the ALT_I2C_SDA_HOLD_IC_SDA_HOLD register field. */
#define ALT_I2C_SDA_HOLD_IC_SDA_HOLD_WIDTH      16
/* The mask used to set the ALT_I2C_SDA_HOLD_IC_SDA_HOLD register field value. */
#define ALT_I2C_SDA_HOLD_IC_SDA_HOLD_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_I2C_SDA_HOLD_IC_SDA_HOLD register field value. */
#define ALT_I2C_SDA_HOLD_IC_SDA_HOLD_CLR_MSK    0xffff0000
/* The reset value of the ALT_I2C_SDA_HOLD_IC_SDA_HOLD register field. */
#define ALT_I2C_SDA_HOLD_IC_SDA_HOLD_RESET      0x1
/* Extracts the ALT_I2C_SDA_HOLD_IC_SDA_HOLD field value from a register. */
#define ALT_I2C_SDA_HOLD_IC_SDA_HOLD_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_I2C_SDA_HOLD_IC_SDA_HOLD register field value suitable for setting the register. */
#define ALT_I2C_SDA_HOLD_IC_SDA_HOLD_SET(value) (((value) << 0) & 0x0000ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_SDA_HOLD.
 */
struct ALT_I2C_SDA_HOLD_s
{
    uint32_t  ic_sda_hold : 16;  /* SDA Hold Bit */
    uint32_t              : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_SDA_HOLD. */
typedef volatile struct ALT_I2C_SDA_HOLD_s  ALT_I2C_SDA_HOLD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_SDA_HOLD register from the beginning of the component. */
#define ALT_I2C_SDA_HOLD_OFST        0x7c
/* The address of the ALT_I2C_SDA_HOLD register. */
#define ALT_I2C_SDA_HOLD_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_SDA_HOLD_OFST))

/*
 * Register : Transmit Abort Source Register - ic_tx_abrt_source
 * 
 * This register has 16 bits that indicate the source of the TX_ABRT bit. Except
 * for Bit 9, this register is cleared whenever the ic_clr_tx_abrt register or the
 * ic_clr_intr register is read. To clear Bit 9, the source of the
 * abrt_sbyte_norstrt must be fixed first; RESTART must be enabled (ic_con[5]=1),
 * the special bit must be cleared (ic_tar[11]), or the gc_or_start bit must be
 * cleared (ic_tar[10]). Once the source of the abrt_sbyte_norstrt is fixed, then
 * this bit can be cleared in the same manner as other bits in this  register. If
 * the source of the abrt_sbyte_norstrt is not fixed before attempting to clear
 * this bit, Bit 9 clears for one cycle and is then re-asserted.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                       
 * :--------|:-------|:------|:-----------------------------------
 *  [0]     | RW     | 0x0   | Master Abort 7 Bit Address        
 *  [1]     | RW     | 0x0   | Master Abort 10 Bit Address Byte 1
 *  [2]     | RW     | 0x0   | Master Abort 10 Bit Address Byte 2
 *  [3]     | RW     | 0x0   | Master Abort TX Noack Bit         
 *  [4]     | RW     | 0x0   | Master Abort GC Noack Bit         
 *  [5]     | RW     | 0x0   | Master Abort GC Read Bit          
 *  [6]     | RW     | 0x0   | Master HS MC Ack                  
 *  [7]     | RW     | 0x0   | Master Abort START Byte           
 *  [8]     | RW     | 0x0   | Master HS Restart Disabled        
 *  [9]     | RW     | 0x0   | Master Abort START No Restart     
 *  [10]    | RW     | 0x0   | Master Abort 10 Bit No Restart    
 *  [11]    | RW     | 0x0   | Master Oper Master Dis            
 *  [12]    | RW     | 0x0   | Master Abort Arbitration Lost     
 *  [13]    | RW     | 0x0   | Slave Abort Flush TXFIFO          
 *  [14]    | RW     | 0x0   | Slave Abort Arbitration Lost      
 *  [15]    | RW     | 0x0   | Slave Abort Read TX               
 *  [31:16] | ???    | 0x0   | *UNDEFINED*                       
 * 
 */
/*
 * Field : Master Abort 7 Bit Address - abrt_7b_addr_noack
 * 
 * Master is in 7-bit addressing mode and the address sent was not acknowledged by
 * any slave. Role of i2c: Master-Transmitter or Master-Receiver
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK_MSB        0
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_7B_ADDR_NOACK_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Master Abort 10 Bit Address Byte 1 - abrt_10addr1_noack
 * 
 * Master is in 10-bit address mode and the first 10-bit address byte was not
 * acknowledged by any slave. Role of i2c: Master-Transmitter or Master-Receiver
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK_MSB        1
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK_SET_MSK    0x00000002
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK_CLR_MSK    0xfffffffd
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR1_NOACK_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Master Abort 10 Bit Address Byte 2 - abrt_10addr2_noack
 * 
 * Master is in 10-bit address mode and the second address byte of the 10-bit
 * address was not acknowledged by any slave. Role of i2c: Master-Transmitter or
 * Master-Receiver
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK_MSB        2
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK_SET_MSK    0x00000004
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK_CLR_MSK    0xfffffffb
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10ADDR2_NOACK_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Master Abort TX Noack Bit - abrt_txdata_noack
 * 
 * This is a master-mode only bit. Master has received an acknowledgement for the
 * address, but when it sent data byte(s) following the address, it did not receive
 * an acknowledge from the remote slave(s). Role of i2c: Master-Transmitter
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK_MSB        3
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK_SET_MSK    0x00000008
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK_CLR_MSK    0xfffffff7
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_TXDATA_NOACK_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Master Abort GC Noack Bit - abrt_gcall_noack
 * 
 * i2c in master mode sent a General Call and no slave on the bus acknowledged the
 * General Call. Role of i2c: Master-Transmitter
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK_MSB        4
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK_SET_MSK    0x00000010
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK_CLR_MSK    0xffffffef
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_NOACK_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Master Abort GC Read Bit - abrt_gcall_read
 * 
 * i2c in master mode sent a General Call but the user programmed the byte
 * following the General Call to be a read from the bus (IC_DATA_CMD[9] is set to
 * 1). Role of i2c: Master-Transmitter
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD_MSB        5
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD_SET_MSK    0x00000020
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD_CLR_MSK    0xffffffdf
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_GCALL_RD_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Master HS MC Ack - abrt_hs_ackdet
 * 
 * Master is in High Speed mode and the High Speed Master code was  acknowledged
 * (wrong behavior). Role of i2c: Master
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET_MSB        6
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET_SET_MSK    0x00000040
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET_CLR_MSK    0xffffffbf
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_ACKDET_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Master Abort START Byte - abrt_sbyte_ackdet
 * 
 * Master has sent a START Byte and the START Byte was acknowledged (wrong
 * behavior). Role of i2c: Master
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET_MSB        7
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET_SET_MSK    0x00000080
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET_CLR_MSK    0xffffff7f
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_ACKDET_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Master HS Restart Disabled - abrt_hs_norstrt
 * 
 * The restart is disabled (IC_RESTART_EN bit (IC_CON[5]) =0) and the user is
 * trying to use the master to transfer data in High Speed mode. Role of i2c:
 * Master-Transmitter or Master-Receiver
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT_MSB        8
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT_SET_MSK    0x00000100
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT_CLR_MSK    0xfffffeff
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_HS_NORSTRT_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Master Abort START No Restart - abrt_sbyte_norstrt
 * 
 * To clear Bit 9, the source of then abrt_sbyte_norstrt must be fixed first;
 * restart must be enabled (ic_con[5]=1), the SPECIAL bit must be cleared
 * (ic_tar[11]), or the GC_OR_START bit must be cleared (ic_tar[10]). Once the
 * source of the abrt_sbyte_norstrt is fixed, then this bit can be cleared in the
 * same manner as other bits in this register. If the source of the
 * abrt_sbyte_norstrt is not fixed before attempting to clear this bit, bit 9
 * clears for one cycle and then gets reasserted. 1: The restart is disabled
 * (IC_RESTART_EN bit (ic_con[5]) =0) and the user is trying to send a START Byte.
 * Role of I2C: Master
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT_MSB        9
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT_SET_MSK    0x00000200
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT_CLR_MSK    0xfffffdff
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SBYTE_NORSTRT_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Master Abort 10 Bit No Restart - abrt_10b_rd_norstrt
 * 
 * The restart is disabled (ic_restart_en bit (ic_con[5]) =0) and the master sends
 * a read command in 10-bit addressing mode. Role of I2C: Master-Receiver
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT_MSB        10
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT_SET_MSK    0x00000400
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT_CLR_MSK    0xfffffbff
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_10B_RD_NORSTRT_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Master Oper Master Dis - abrt_master_dis
 * 
 * User tries to initiate a Master operation with the Master mode disabled. Role of
 * I2C: Master-Transmitter or Master-Receiver
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS_MSB        11
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS_SET_MSK    0x00000800
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_MST_DIS_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : Master Abort Arbitration Lost - arb_lost
 * 
 * Master has lost arbitration, or if IC_TX_ABRT_SOURCE[14] is also set, then the
 * slave transmitter has lost arbitration. Note: I2C can be both master and slave
 * at the same time. Role of i2c: Master-Transmitter or Slave-Transmitter
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ARB_LOST register field. */
#define ALT_I2C_TX_ABRT_SRC_ARB_LOST_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ARB_LOST register field. */
#define ALT_I2C_TX_ABRT_SRC_ARB_LOST_MSB        12
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ARB_LOST register field. */
#define ALT_I2C_TX_ABRT_SRC_ARB_LOST_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ARB_LOST register field value. */
#define ALT_I2C_TX_ABRT_SRC_ARB_LOST_SET_MSK    0x00001000
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ARB_LOST register field value. */
#define ALT_I2C_TX_ABRT_SRC_ARB_LOST_CLR_MSK    0xffffefff
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ARB_LOST register field. */
#define ALT_I2C_TX_ABRT_SRC_ARB_LOST_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ARB_LOST field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ARB_LOST_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_I2C_TX_ABRT_SRC_ARB_LOST register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ARB_LOST_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : Slave Abort Flush TXFIFO - abrt_slvflush_txfifo
 * 
 * Slave has received a read command and some data exists in the TX FIFO so the
 * slave issues a TX_ABRT interrupt to flush old data in TX FIFO. Role of I2C:
 * Slave-Transmitter
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO_MSB        13
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO_SET_MSK    0x00002000
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO_CLR_MSK    0xffffdfff
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVFLUSH_TXFIFO_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : Slave Abort Arbitration Lost - abrt_slv_arblost
 * 
 * Slave lost the bus while transmitting data to a remote master.
 * IC_TX_ABRT_SOURCE[12] is set at the same time. Note: Even though the slave never
 * 'owns' the bus, something could go wrong on the bus. This is a fail safe check.
 * For instance, during a data transmission at the low-to-high transition of SCL,
 * if what is on the data bus is not what is supposed to be transmitted, then i2c
 * no longer own the bus. Role of I2C: Slave-Transmitter
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST_MSB        14
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST_SET_MSK    0x00004000
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST_CLR_MSK    0xffffbfff
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLV_ARBLOST_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : Slave Abort Read TX - abrt_slvrd_intx
 * 
 * When the processor side responds to a slave mode request for data to be
 * transmitted to a remote master and user writes a 1 in CMD (bit 8) of IC_DATA_CMD
 * register. Role of I2C: Slave-Transmitter
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX_MSB        15
/* The width in bits of the ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX_WIDTH      1
/* The mask used to set the ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX_SET_MSK    0x00008000
/* The mask used to clear the ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX register field value. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX_CLR_MSK    0xffff7fff
/* The reset value of the ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX register field. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX_RESET      0x0
/* Extracts the ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX field value from a register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX register field value suitable for setting the register. */
#define ALT_I2C_TX_ABRT_SRC_ABRT_SLVRD_INTX_SET(value) (((value) << 15) & 0x00008000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_TX_ABRT_SRC.
 */
struct ALT_I2C_TX_ABRT_SRC_s
{
    uint32_t  abrt_7b_addr_noack   :  1;  /* Master Abort 7 Bit Address */
    uint32_t  abrt_10addr1_noack   :  1;  /* Master Abort 10 Bit Address Byte 1 */
    uint32_t  abrt_10addr2_noack   :  1;  /* Master Abort 10 Bit Address Byte 2 */
    uint32_t  abrt_txdata_noack    :  1;  /* Master Abort TX Noack Bit */
    uint32_t  abrt_gcall_noack     :  1;  /* Master Abort GC Noack Bit */
    uint32_t  abrt_gcall_read      :  1;  /* Master Abort GC Read Bit */
    uint32_t  abrt_hs_ackdet       :  1;  /* Master HS MC Ack */
    uint32_t  abrt_sbyte_ackdet    :  1;  /* Master Abort START Byte */
    uint32_t  abrt_hs_norstrt      :  1;  /* Master HS Restart Disabled */
    uint32_t  abrt_sbyte_norstrt   :  1;  /* Master Abort START No Restart */
    uint32_t  abrt_10b_rd_norstrt  :  1;  /* Master Abort 10 Bit No Restart */
    uint32_t  abrt_master_dis      :  1;  /* Master Oper Master Dis */
    uint32_t  arb_lost             :  1;  /* Master Abort Arbitration Lost */
    uint32_t  abrt_slvflush_txfifo :  1;  /* Slave Abort Flush TXFIFO */
    uint32_t  abrt_slv_arblost     :  1;  /* Slave Abort Arbitration Lost */
    uint32_t  abrt_slvrd_intx      :  1;  /* Slave Abort Read TX */
    uint32_t                       : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_TX_ABRT_SRC. */
typedef volatile struct ALT_I2C_TX_ABRT_SRC_s  ALT_I2C_TX_ABRT_SRC_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_TX_ABRT_SRC register from the beginning of the component. */
#define ALT_I2C_TX_ABRT_SRC_OFST        0x80
/* The address of the ALT_I2C_TX_ABRT_SRC register. */
#define ALT_I2C_TX_ABRT_SRC_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_TX_ABRT_SRC_OFST))

/*
 * Register : Generate Slave Data NACK - ic_slv_data_nack_only
 * 
 * The register is used to generate a NACK for the data part of a transfer when i2c
 * is acting as a slave-receiver.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description      
 * :-------|:-------|:------|:------------------
 *  [0]    | RW     | 0x0   | Generate Nack Bit
 *  [31:1] | ???    | 0x0   | *UNDEFINED*      
 * 
 */
/*
 * Field : Generate Nack Bit - nack
 * 
 * This Bit control Nack generation
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                         | Value | Description                          
 * :---------------------------------------------|:------|:--------------------------------------
 *  ALT_I2C_SLV_DATA_NACK_ONLY_NACK_E_AFTERDBYTE | 0x1   | Generate NACK after data byte receive
 *  ALT_I2C_SLV_DATA_NACK_ONLY_NACK_E_NORM       | 0x0   | Generate NACK/ACK normally           
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_SLV_DATA_NACK_ONLY_NACK
 * 
 * Generate NACK after data byte receive
 */
#define ALT_I2C_SLV_DATA_NACK_ONLY_NACK_E_AFTERDBYTE    0x1
/*
 * Enumerated value for register field ALT_I2C_SLV_DATA_NACK_ONLY_NACK
 * 
 * Generate NACK/ACK normally
 */
#define ALT_I2C_SLV_DATA_NACK_ONLY_NACK_E_NORM          0x0

/* The Least Significant Bit (LSB) position of the ALT_I2C_SLV_DATA_NACK_ONLY_NACK register field. */
#define ALT_I2C_SLV_DATA_NACK_ONLY_NACK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_SLV_DATA_NACK_ONLY_NACK register field. */
#define ALT_I2C_SLV_DATA_NACK_ONLY_NACK_MSB        0
/* The width in bits of the ALT_I2C_SLV_DATA_NACK_ONLY_NACK register field. */
#define ALT_I2C_SLV_DATA_NACK_ONLY_NACK_WIDTH      1
/* The mask used to set the ALT_I2C_SLV_DATA_NACK_ONLY_NACK register field value. */
#define ALT_I2C_SLV_DATA_NACK_ONLY_NACK_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_SLV_DATA_NACK_ONLY_NACK register field value. */
#define ALT_I2C_SLV_DATA_NACK_ONLY_NACK_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_SLV_DATA_NACK_ONLY_NACK register field. */
#define ALT_I2C_SLV_DATA_NACK_ONLY_NACK_RESET      0x0
/* Extracts the ALT_I2C_SLV_DATA_NACK_ONLY_NACK field value from a register. */
#define ALT_I2C_SLV_DATA_NACK_ONLY_NACK_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_SLV_DATA_NACK_ONLY_NACK register field value suitable for setting the register. */
#define ALT_I2C_SLV_DATA_NACK_ONLY_NACK_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_SLV_DATA_NACK_ONLY.
 */
struct ALT_I2C_SLV_DATA_NACK_ONLY_s
{
    uint32_t  nack :  1;  /* Generate Nack Bit */
    uint32_t       : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_SLV_DATA_NACK_ONLY. */
typedef volatile struct ALT_I2C_SLV_DATA_NACK_ONLY_s  ALT_I2C_SLV_DATA_NACK_ONLY_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_SLV_DATA_NACK_ONLY register from the beginning of the component. */
#define ALT_I2C_SLV_DATA_NACK_ONLY_OFST        0x84
/* The address of the ALT_I2C_SLV_DATA_NACK_ONLY register. */
#define ALT_I2C_SLV_DATA_NACK_ONLY_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_SLV_DATA_NACK_ONLY_OFST))

/*
 * Register : DMA Control - ic_dma_cr
 * 
 * The register is used to enable the DMA Controller interface operation. There is
 * a separate bit for transmit and receive. This can be programmed regardless of
 * the state of IC_ENABLE.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description            
 * :-------|:-------|:------|:------------------------
 *  [0]    | RW     | 0x0   | Receive DMA Enable Bit 
 *  [1]    | RW     | 0x0   | Transmit DMA Enable Bit
 *  [31:2] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : Receive DMA Enable Bit - rdmae
 * 
 * This bit enables/disables the receive FIFO DMA channel.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description        
 * :---------------------------|:------|:--------------------
 *  ALT_I2C_DMA_CR_RDMAE_E_DIS | 0x0   | Receive DMA disable
 *  ALT_I2C_DMA_CR_RDMAE_E_EN  | 0x1   | Receive DMA enabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_DMA_CR_RDMAE
 * 
 * Receive DMA disable
 */
#define ALT_I2C_DMA_CR_RDMAE_E_DIS  0x0
/*
 * Enumerated value for register field ALT_I2C_DMA_CR_RDMAE
 * 
 * Receive DMA enabled
 */
#define ALT_I2C_DMA_CR_RDMAE_E_EN   0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_DMA_CR_RDMAE register field. */
#define ALT_I2C_DMA_CR_RDMAE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_DMA_CR_RDMAE register field. */
#define ALT_I2C_DMA_CR_RDMAE_MSB        0
/* The width in bits of the ALT_I2C_DMA_CR_RDMAE register field. */
#define ALT_I2C_DMA_CR_RDMAE_WIDTH      1
/* The mask used to set the ALT_I2C_DMA_CR_RDMAE register field value. */
#define ALT_I2C_DMA_CR_RDMAE_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_DMA_CR_RDMAE register field value. */
#define ALT_I2C_DMA_CR_RDMAE_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_DMA_CR_RDMAE register field. */
#define ALT_I2C_DMA_CR_RDMAE_RESET      0x0
/* Extracts the ALT_I2C_DMA_CR_RDMAE field value from a register. */
#define ALT_I2C_DMA_CR_RDMAE_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_DMA_CR_RDMAE register field value suitable for setting the register. */
#define ALT_I2C_DMA_CR_RDMAE_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Transmit DMA Enable Bit - tdmae
 * 
 * This bit enables/disables the transmit FIFO DMA channel.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                       | Value | Description         
 * :---------------------------|:------|:---------------------
 *  ALT_I2C_DMA_CR_TDMAE_E_DIS | 0x0   | Transmit DMA disable
 *  ALT_I2C_DMA_CR_TDMAE_E_EN  | 0x1   | Transmit DMA enabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_DMA_CR_TDMAE
 * 
 * Transmit DMA disable
 */
#define ALT_I2C_DMA_CR_TDMAE_E_DIS  0x0
/*
 * Enumerated value for register field ALT_I2C_DMA_CR_TDMAE
 * 
 * Transmit DMA enabled
 */
#define ALT_I2C_DMA_CR_TDMAE_E_EN   0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_DMA_CR_TDMAE register field. */
#define ALT_I2C_DMA_CR_TDMAE_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_I2C_DMA_CR_TDMAE register field. */
#define ALT_I2C_DMA_CR_TDMAE_MSB        1
/* The width in bits of the ALT_I2C_DMA_CR_TDMAE register field. */
#define ALT_I2C_DMA_CR_TDMAE_WIDTH      1
/* The mask used to set the ALT_I2C_DMA_CR_TDMAE register field value. */
#define ALT_I2C_DMA_CR_TDMAE_SET_MSK    0x00000002
/* The mask used to clear the ALT_I2C_DMA_CR_TDMAE register field value. */
#define ALT_I2C_DMA_CR_TDMAE_CLR_MSK    0xfffffffd
/* The reset value of the ALT_I2C_DMA_CR_TDMAE register field. */
#define ALT_I2C_DMA_CR_TDMAE_RESET      0x0
/* Extracts the ALT_I2C_DMA_CR_TDMAE field value from a register. */
#define ALT_I2C_DMA_CR_TDMAE_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_I2C_DMA_CR_TDMAE register field value suitable for setting the register. */
#define ALT_I2C_DMA_CR_TDMAE_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_DMA_CR.
 */
struct ALT_I2C_DMA_CR_s
{
    uint32_t  rdmae :  1;  /* Receive DMA Enable Bit */
    uint32_t  tdmae :  1;  /* Transmit DMA Enable Bit */
    uint32_t        : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_DMA_CR. */
typedef volatile struct ALT_I2C_DMA_CR_s  ALT_I2C_DMA_CR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_DMA_CR register from the beginning of the component. */
#define ALT_I2C_DMA_CR_OFST        0x88
/* The address of the ALT_I2C_DMA_CR register. */
#define ALT_I2C_DMA_CR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_DMA_CR_OFST))

/*
 * Register : DMA Transmit Data Level - ic_dma_tdlr
 * 
 * This register supports DMA Transmit Operation.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                
 * :-------|:-------|:------|:----------------------------
 *  [5:0]  | RW     | 0x0   | DMA Transmit Data Level Bit
 *  [31:6] | ???    | 0x0   | *UNDEFINED*                
 * 
 */
/*
 * Field : DMA Transmit Data Level Bit - dmatdl
 * 
 * This bit field controls the level at which a DMA request is made by the transmit
 * logic. It is equal to the watermark level; that is, the i2c_dma_tx_req signal is
 * generated when the number of valid data entries in the transmit FIFO is equal to
 * or below this field value, and TDMAE = 1.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_DMA_TDLR_DMATDL register field. */
#define ALT_I2C_DMA_TDLR_DMATDL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_DMA_TDLR_DMATDL register field. */
#define ALT_I2C_DMA_TDLR_DMATDL_MSB        5
/* The width in bits of the ALT_I2C_DMA_TDLR_DMATDL register field. */
#define ALT_I2C_DMA_TDLR_DMATDL_WIDTH      6
/* The mask used to set the ALT_I2C_DMA_TDLR_DMATDL register field value. */
#define ALT_I2C_DMA_TDLR_DMATDL_SET_MSK    0x0000003f
/* The mask used to clear the ALT_I2C_DMA_TDLR_DMATDL register field value. */
#define ALT_I2C_DMA_TDLR_DMATDL_CLR_MSK    0xffffffc0
/* The reset value of the ALT_I2C_DMA_TDLR_DMATDL register field. */
#define ALT_I2C_DMA_TDLR_DMATDL_RESET      0x0
/* Extracts the ALT_I2C_DMA_TDLR_DMATDL field value from a register. */
#define ALT_I2C_DMA_TDLR_DMATDL_GET(value) (((value) & 0x0000003f) >> 0)
/* Produces a ALT_I2C_DMA_TDLR_DMATDL register field value suitable for setting the register. */
#define ALT_I2C_DMA_TDLR_DMATDL_SET(value) (((value) << 0) & 0x0000003f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_DMA_TDLR.
 */
struct ALT_I2C_DMA_TDLR_s
{
    uint32_t  dmatdl :  6;  /* DMA Transmit Data Level Bit */
    uint32_t         : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_DMA_TDLR. */
typedef volatile struct ALT_I2C_DMA_TDLR_s  ALT_I2C_DMA_TDLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_DMA_TDLR register from the beginning of the component. */
#define ALT_I2C_DMA_TDLR_OFST        0x8c
/* The address of the ALT_I2C_DMA_TDLR register. */
#define ALT_I2C_DMA_TDLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_DMA_TDLR_OFST))

/*
 * Register : Receive Data Level - ic_dma_rdlr
 * 
 * DMA Control Signals Interface.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description            
 * :-------|:-------|:------|:------------------------
 *  [5:0]  | RW     | 0x0   | Receive Data Level Bits
 *  [31:6] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : Receive Data Level Bits - dmardl
 * 
 * This bit field controls the level at which a DMA request is made by the receive
 * logic. The watermark level \= DMARDL+1; that is, dma_rx_req is generated when
 * the number of valid data entries in the receive FIFO is equal to or more than
 * this field value + 1, and RDMAE =1. For instance, when DMARDL is 0, then
 * dma_rx_req is asserted when or more data entries are present in the receive
 * FIFO.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_DMA_RDLR_DMARDL register field. */
#define ALT_I2C_DMA_RDLR_DMARDL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_DMA_RDLR_DMARDL register field. */
#define ALT_I2C_DMA_RDLR_DMARDL_MSB        5
/* The width in bits of the ALT_I2C_DMA_RDLR_DMARDL register field. */
#define ALT_I2C_DMA_RDLR_DMARDL_WIDTH      6
/* The mask used to set the ALT_I2C_DMA_RDLR_DMARDL register field value. */
#define ALT_I2C_DMA_RDLR_DMARDL_SET_MSK    0x0000003f
/* The mask used to clear the ALT_I2C_DMA_RDLR_DMARDL register field value. */
#define ALT_I2C_DMA_RDLR_DMARDL_CLR_MSK    0xffffffc0
/* The reset value of the ALT_I2C_DMA_RDLR_DMARDL register field. */
#define ALT_I2C_DMA_RDLR_DMARDL_RESET      0x0
/* Extracts the ALT_I2C_DMA_RDLR_DMARDL field value from a register. */
#define ALT_I2C_DMA_RDLR_DMARDL_GET(value) (((value) & 0x0000003f) >> 0)
/* Produces a ALT_I2C_DMA_RDLR_DMARDL register field value suitable for setting the register. */
#define ALT_I2C_DMA_RDLR_DMARDL_SET(value) (((value) << 0) & 0x0000003f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_DMA_RDLR.
 */
struct ALT_I2C_DMA_RDLR_s
{
    uint32_t  dmardl :  6;  /* Receive Data Level Bits */
    uint32_t         : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_DMA_RDLR. */
typedef volatile struct ALT_I2C_DMA_RDLR_s  ALT_I2C_DMA_RDLR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_DMA_RDLR register from the beginning of the component. */
#define ALT_I2C_DMA_RDLR_OFST        0x90
/* The address of the ALT_I2C_DMA_RDLR register. */
#define ALT_I2C_DMA_RDLR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_DMA_RDLR_OFST))

/*
 * Register : SDA Setup Register - ic_sda_setup
 * 
 * This register controls the amount of time delay (in terms of number of l4_sp_clk
 * clock periods) introduced in the rising edge of SCL relative to SDA changing by
 * holding SCL low when I2C services a read request while operating as a slave-
 * transmitter. The relevant I2C requirement is tSU:DAT (note 4) as detailed in the
 * I2C Bus Specification. This register must be programmed with a value equal to or
 * greater than 2.
 * 
 * Note: The length of setup time is calculated using [(IC_SDA_SETUP - 1) *
 * (l4_sp_clk)], so if the user requires 10 l4_sp_clk periods of setup time, they
 * should program a value of 11. The IC_SDA_SETUP register is only used by the I2C
 * when operating as a slave transmitter.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description    
 * :-------|:-------|:------|:----------------
 *  [7:0]  | RW     | 0x64  | SDA Setup Value
 *  [31:8] | ???    | 0x0   | *UNDEFINED*    
 * 
 */
/*
 * Field : SDA Setup Value - sda_setup
 * 
 * It is recommended that if the required delay is 1000ns, then for an l4_sp_clk
 * frequency of 10 MHz, ic_sda_setup should be programmed to a value of 11.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_SDA_SETUP_SDA_SETUP register field. */
#define ALT_I2C_SDA_SETUP_SDA_SETUP_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_SDA_SETUP_SDA_SETUP register field. */
#define ALT_I2C_SDA_SETUP_SDA_SETUP_MSB        7
/* The width in bits of the ALT_I2C_SDA_SETUP_SDA_SETUP register field. */
#define ALT_I2C_SDA_SETUP_SDA_SETUP_WIDTH      8
/* The mask used to set the ALT_I2C_SDA_SETUP_SDA_SETUP register field value. */
#define ALT_I2C_SDA_SETUP_SDA_SETUP_SET_MSK    0x000000ff
/* The mask used to clear the ALT_I2C_SDA_SETUP_SDA_SETUP register field value. */
#define ALT_I2C_SDA_SETUP_SDA_SETUP_CLR_MSK    0xffffff00
/* The reset value of the ALT_I2C_SDA_SETUP_SDA_SETUP register field. */
#define ALT_I2C_SDA_SETUP_SDA_SETUP_RESET      0x64
/* Extracts the ALT_I2C_SDA_SETUP_SDA_SETUP field value from a register. */
#define ALT_I2C_SDA_SETUP_SDA_SETUP_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_I2C_SDA_SETUP_SDA_SETUP register field value suitable for setting the register. */
#define ALT_I2C_SDA_SETUP_SDA_SETUP_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_SDA_SETUP.
 */
struct ALT_I2C_SDA_SETUP_s
{
    uint32_t  sda_setup :  8;  /* SDA Setup Value */
    uint32_t            : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_SDA_SETUP. */
typedef volatile struct ALT_I2C_SDA_SETUP_s  ALT_I2C_SDA_SETUP_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_SDA_SETUP register from the beginning of the component. */
#define ALT_I2C_SDA_SETUP_OFST        0x94
/* The address of the ALT_I2C_SDA_SETUP register. */
#define ALT_I2C_SDA_SETUP_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_SDA_SETUP_OFST))

/*
 * Register : ACK General Call - ic_ack_general_call
 * 
 * The register controls whether i2c responds with a ACK or NACK when it receives
 * an I2C General Call address.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description         
 * :-------|:-------|:------|:---------------------
 *  [0]    | RW     | 0x1   | ACK General Call Bit
 *  [31:1] | ???    | 0x0   | *UNDEFINED*         
 * 
 */
/*
 * Field : ACK General Call Bit - ack_gen_call
 * 
 * When an ACK is asserted, (by asserting i2c_out_data) when it receives a General
 * call. Otherwise, i2c responds with a NACK (by negating i2c_out_data).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                         | Value | Description             
 * :---------------------------------------------|:------|:-------------------------
 *  ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL_E_NACK | 0x0   | I2C responds with a NACK
 *  ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL_E_ACK  | 0x1   | I2C responds with an ACK
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL
 * 
 * I2C responds with a NACK
 */
#define ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL_E_NACK    0x0
/*
 * Enumerated value for register field ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL
 * 
 * I2C responds with an ACK
 */
#define ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL_E_ACK     0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL register field. */
#define ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL register field. */
#define ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL_MSB        0
/* The width in bits of the ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL register field. */
#define ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL_WIDTH      1
/* The mask used to set the ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL register field value. */
#define ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL register field value. */
#define ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL register field. */
#define ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL_RESET      0x1
/* Extracts the ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL field value from a register. */
#define ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL register field value suitable for setting the register. */
#define ALT_I2C_ACK_GENERAL_CALL_ACK_GEN_CALL_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_ACK_GENERAL_CALL.
 */
struct ALT_I2C_ACK_GENERAL_CALL_s
{
    uint32_t  ack_gen_call :  1;  /* ACK General Call Bit */
    uint32_t               : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_ACK_GENERAL_CALL. */
typedef volatile struct ALT_I2C_ACK_GENERAL_CALL_s  ALT_I2C_ACK_GENERAL_CALL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_ACK_GENERAL_CALL register from the beginning of the component. */
#define ALT_I2C_ACK_GENERAL_CALL_OFST        0x98
/* The address of the ALT_I2C_ACK_GENERAL_CALL register. */
#define ALT_I2C_ACK_GENERAL_CALL_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_ACK_GENERAL_CALL_OFST))

/*
 * Register : Enable Status Register - ic_enable_status
 * 
 * This register is used to report the i2c hardware status when the IC_ENABLE
 * register is set from 1 to 0; that is, when i2c is disabled. If IC_ENABLE has
 * been set to 1, bits 2:1 are forced to 0, and bit 0 is forced to 1. If IC_ENABLE
 * has been set to 0, bits 2:1 are only valid as soon as bit 0 is read as '0'.
 * 
 * Note: When ic_enable has been written with '0' a delay occurs for bit 0 to be
 * read as '0' because disabling the i2c depends on I2C bus activities.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [0]    | R      | 0x0   | Enable Status Bit            
 *  [1]    | R      | 0x0   | Slave Disabled While Busy Bit
 *  [2]    | R      | 0x0   | Slave Received Data Lost Bit 
 *  [31:3] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : Enable Status Bit - ic_en
 * 
 * This bit always reflects the value driven on the output port ic_en. Not used in
 * current application. When read as 1, i2c is deemed to be in an enabled state.
 * When read as 0, i2c is deemed completely inactive. NOTE: The CPU can safely read
 * this bit anytime. When this bit is read as 0, the CPU can safely read
 * slv_rx_data_lost (bit 2) and slv_disabled_while_busy (bit 1).
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_EN_STAT_IC_EN register field. */
#define ALT_I2C_EN_STAT_IC_EN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_EN_STAT_IC_EN register field. */
#define ALT_I2C_EN_STAT_IC_EN_MSB        0
/* The width in bits of the ALT_I2C_EN_STAT_IC_EN register field. */
#define ALT_I2C_EN_STAT_IC_EN_WIDTH      1
/* The mask used to set the ALT_I2C_EN_STAT_IC_EN register field value. */
#define ALT_I2C_EN_STAT_IC_EN_SET_MSK    0x00000001
/* The mask used to clear the ALT_I2C_EN_STAT_IC_EN register field value. */
#define ALT_I2C_EN_STAT_IC_EN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_I2C_EN_STAT_IC_EN register field. */
#define ALT_I2C_EN_STAT_IC_EN_RESET      0x0
/* Extracts the ALT_I2C_EN_STAT_IC_EN field value from a register. */
#define ALT_I2C_EN_STAT_IC_EN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_I2C_EN_STAT_IC_EN register field value suitable for setting the register. */
#define ALT_I2C_EN_STAT_IC_EN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Slave Disabled While Busy Bit - slv_disabled_while_busy
 * 
 * This bit indicates if a potential or active Slave operation has been aborted due
 * to the setting of the ic_enable register from 1 to 0. This bit is set when the
 * CPU writes a 0 to the ic_enable register while: (a) I2C is receiving the address
 * byte of the Slave-Transmitter operation from a remote master; OR, (b) address
 * and data bytes of the Slave-Receiver operation from a remote master. When read
 * as 1, I2C is deemed to have forced a NACK during any part of an I2C transfer,
 * irrespective of whether the I2C address matches the slave address set in i2c
 * (IC_SAR register) OR if the transfer is completed before IC_ENABLE is set to 0
 * but has not taken effect. NOTE: If the remote I2C master terminates the transfer
 * with a STOP condition before the i2c has a chance to NACK a transfer, and
 * IC_ENABLE has been set to 0, then this bit will also be set to 1. When read as
 * 0, i2c is deemed to have been disabled when there is master activity, or when
 * the I2C bus is idle. NOTE: The CPU can safely read this bit when IC_EN (bit 0)
 * is read as 0.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY register field. */
#define ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY register field. */
#define ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY_MSB        1
/* The width in bits of the ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY register field. */
#define ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY_WIDTH      1
/* The mask used to set the ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY register field value. */
#define ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY_SET_MSK    0x00000002
/* The mask used to clear the ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY register field value. */
#define ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY_CLR_MSK    0xfffffffd
/* The reset value of the ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY register field. */
#define ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY_RESET      0x0
/* Extracts the ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY field value from a register. */
#define ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY register field value suitable for setting the register. */
#define ALT_I2C_EN_STAT_SLV_DISD_WHILE_BUSY_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Slave Received Data Lost Bit - slv_rx_data_lost
 * 
 * This bit indicates if a Slave-Receiver operation has been aborted with at least
 * one data byte received from an I2C transfer due to the setting of IC ENABLE from
 * 1 to 0. When read as 1, i2c is deemed to have been actively engaged in an
 * aborted I2C transfer (with matching address) and the data phase of the I2C
 * transfer has been entered, even though a data byte has been responded with a
 * NACK. NOTE: If the remote I2C master terminates the transfer with a STOP
 * condition before the i2c has a chance to NACK a transfer, and ic_enable has been
 * set to 0, then this bit is also set to 1. When read as 0, i2c is deemed to have
 * been disabled without being actively involved in the data phase of a Slave-
 * Receiver transfer. NOTE: The CPU can safely read this bit when IC_EN (bit 0) is
 * read as 0.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_EN_STAT_SLV_RX_DATA_LOST register field. */
#define ALT_I2C_EN_STAT_SLV_RX_DATA_LOST_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_I2C_EN_STAT_SLV_RX_DATA_LOST register field. */
#define ALT_I2C_EN_STAT_SLV_RX_DATA_LOST_MSB        2
/* The width in bits of the ALT_I2C_EN_STAT_SLV_RX_DATA_LOST register field. */
#define ALT_I2C_EN_STAT_SLV_RX_DATA_LOST_WIDTH      1
/* The mask used to set the ALT_I2C_EN_STAT_SLV_RX_DATA_LOST register field value. */
#define ALT_I2C_EN_STAT_SLV_RX_DATA_LOST_SET_MSK    0x00000004
/* The mask used to clear the ALT_I2C_EN_STAT_SLV_RX_DATA_LOST register field value. */
#define ALT_I2C_EN_STAT_SLV_RX_DATA_LOST_CLR_MSK    0xfffffffb
/* The reset value of the ALT_I2C_EN_STAT_SLV_RX_DATA_LOST register field. */
#define ALT_I2C_EN_STAT_SLV_RX_DATA_LOST_RESET      0x0
/* Extracts the ALT_I2C_EN_STAT_SLV_RX_DATA_LOST field value from a register. */
#define ALT_I2C_EN_STAT_SLV_RX_DATA_LOST_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_I2C_EN_STAT_SLV_RX_DATA_LOST register field value suitable for setting the register. */
#define ALT_I2C_EN_STAT_SLV_RX_DATA_LOST_SET(value) (((value) << 2) & 0x00000004)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_EN_STAT.
 */
struct ALT_I2C_EN_STAT_s
{
    const uint32_t  ic_en                   :  1;  /* Enable Status Bit */
    const uint32_t  slv_disabled_while_busy :  1;  /* Slave Disabled While Busy Bit */
    const uint32_t  slv_rx_data_lost        :  1;  /* Slave Received Data Lost Bit */
    uint32_t                                : 29;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_EN_STAT. */
typedef volatile struct ALT_I2C_EN_STAT_s  ALT_I2C_EN_STAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_EN_STAT register from the beginning of the component. */
#define ALT_I2C_EN_STAT_OFST        0x9c
/* The address of the ALT_I2C_EN_STAT register. */
#define ALT_I2C_EN_STAT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_EN_STAT_OFST))

/*
 * Register : SS and FS Spike Suppression Limit Register - ic_fs_spklen
 * 
 * This register is used to store the duration, measured in ic_clk cycles, of the
 * longest spike that is filtered out by the spike suppression logic when the
 * component is operating in SS or FS modes.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                     
 * :-------|:-------|:------|:---------------------------------
 *  [7:0]  | RW     | 0x2   | Spike Suppression Limit Register
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                     
 * 
 */
/*
 * Field : Spike Suppression Limit Register - spklen
 * 
 * This register must be set before any I2C bus transaction can take place to
 * ensure stable operation. This register sets the duration, measured in ic_clk
 * cycles, of the longest spike in the SCL or SDA lines that are filtered out by
 * the spike suppression logic. This register can be written only when the I2C
 * interface is disabled, which corresponds to the IC_ENABLE register being set to
 * 0. Writes at other times have no effect. The minimum valid value is 1; hardware
 * prevents values less than this being written, and if attempted results in 2
 * being set.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_FS_SPKLEN_SPKLEN register field. */
#define ALT_I2C_FS_SPKLEN_SPKLEN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_FS_SPKLEN_SPKLEN register field. */
#define ALT_I2C_FS_SPKLEN_SPKLEN_MSB        7
/* The width in bits of the ALT_I2C_FS_SPKLEN_SPKLEN register field. */
#define ALT_I2C_FS_SPKLEN_SPKLEN_WIDTH      8
/* The mask used to set the ALT_I2C_FS_SPKLEN_SPKLEN register field value. */
#define ALT_I2C_FS_SPKLEN_SPKLEN_SET_MSK    0x000000ff
/* The mask used to clear the ALT_I2C_FS_SPKLEN_SPKLEN register field value. */
#define ALT_I2C_FS_SPKLEN_SPKLEN_CLR_MSK    0xffffff00
/* The reset value of the ALT_I2C_FS_SPKLEN_SPKLEN register field. */
#define ALT_I2C_FS_SPKLEN_SPKLEN_RESET      0x2
/* Extracts the ALT_I2C_FS_SPKLEN_SPKLEN field value from a register. */
#define ALT_I2C_FS_SPKLEN_SPKLEN_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_I2C_FS_SPKLEN_SPKLEN register field value suitable for setting the register. */
#define ALT_I2C_FS_SPKLEN_SPKLEN_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_FS_SPKLEN.
 */
struct ALT_I2C_FS_SPKLEN_s
{
    uint32_t  spklen :  8;  /* Spike Suppression Limit Register */
    uint32_t         : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_FS_SPKLEN. */
typedef volatile struct ALT_I2C_FS_SPKLEN_s  ALT_I2C_FS_SPKLEN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_FS_SPKLEN register from the beginning of the component. */
#define ALT_I2C_FS_SPKLEN_OFST        0xa0
/* The address of the ALT_I2C_FS_SPKLEN register. */
#define ALT_I2C_FS_SPKLEN_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_FS_SPKLEN_OFST))

/*
 * Register : Component Parameter Register 1 - ic_comp_param_1
 * 
 * This is a constant read-only register that contains encoded information about
 * the component's parameter settings.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description            
 * :--------|:-------|:------|:------------------------
 *  [1:0]   | R      | 0x2   | APB Data Width Register
 *  [3:2]   | R      | 0x2   | Max Speed Mode         
 *  [4]     | R      | 0x0   | CNT Registers Access   
 *  [5]     | R      | 0x1   | Intr IO                
 *  [6]     | R      | 0x1   | Has DMA                
 *  [7]     | R      | 0x1   | Add Encoded Params     
 *  [15:8]  | R      | 0x3f  | Rx Buffer Depth        
 *  [23:16] | R      | 0x3f  | Tx Buffer Depth        
 *  [31:24] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : APB Data Width Register - apb_data_width
 * 
 * Sets the APB Data Width.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                              | Value | Description              
 * :--------------------------------------------------|:------|:--------------------------
 *  ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH_E_WIDTH32BITS | 0x2   | APB Data Width is 32 Bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH
 * 
 * APB Data Width is 32 Bits
 */
#define ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH_E_WIDTH32BITS   0x2

/* The Least Significant Bit (LSB) position of the ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH register field. */
#define ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH register field. */
#define ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH_MSB        1
/* The width in bits of the ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH register field. */
#define ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH_WIDTH      2
/* The mask used to set the ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH register field value. */
#define ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH_SET_MSK    0x00000003
/* The mask used to clear the ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH register field value. */
#define ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH_CLR_MSK    0xfffffffc
/* The reset value of the ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH register field. */
#define ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH_RESET      0x2
/* Extracts the ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH field value from a register. */
#define ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH register field value suitable for setting the register. */
#define ALT_I2C_COMP_PARAM_1_APB_DATA_WIDTH_SET(value) (((value) << 0) & 0x00000003)

/*
 * Field : Max Speed Mode - max_speed_mode
 * 
 * The value of this field determines the maximum i2c bus interface speed.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description           
 * :------------------------------------------|:------|:-----------------------
 *  ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD_E_FAST | 0x2   | Fast Mode (400 kbit/s)
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD
 * 
 * Fast Mode (400 kbit/s)
 */
#define ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD_E_FAST   0x2

/* The Least Significant Bit (LSB) position of the ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD register field. */
#define ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD register field. */
#define ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD_MSB        3
/* The width in bits of the ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD register field. */
#define ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD_WIDTH      2
/* The mask used to set the ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD register field value. */
#define ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD_SET_MSK    0x0000000c
/* The mask used to clear the ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD register field value. */
#define ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD_CLR_MSK    0xfffffff3
/* The reset value of the ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD register field. */
#define ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD_RESET      0x2
/* Extracts the ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD field value from a register. */
#define ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD_GET(value) (((value) & 0x0000000c) >> 2)
/* Produces a ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD register field value suitable for setting the register. */
#define ALT_I2C_COMP_PARAM_1_MAX_SPEED_MOD_SET(value) (((value) << 2) & 0x0000000c)

/*
 * Field : CNT Registers Access - hc_count_values
 * 
 * This makes the *CNT registers readable and writable.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                        | Value | Description              
 * :--------------------------------------------|:------|:--------------------------
 *  ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES_E_RDWR | 0x0   | *CNT registers read/write
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES
 * 
 * * CNT registers read/write
 */
#define ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES_E_RDWR 0x0

/* The Least Significant Bit (LSB) position of the ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES register field. */
#define ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES register field. */
#define ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES_MSB        4
/* The width in bits of the ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES register field. */
#define ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES_WIDTH      1
/* The mask used to set the ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES register field value. */
#define ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES_SET_MSK    0x00000010
/* The mask used to clear the ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES register field value. */
#define ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES_CLR_MSK    0xffffffef
/* The reset value of the ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES register field. */
#define ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES_RESET      0x0
/* Extracts the ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES field value from a register. */
#define ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES register field value suitable for setting the register. */
#define ALT_I2C_COMP_PARAM_1_HC_COUNT_VALUES_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Intr IO - intr_io
 * 
 * All interrupt sources are combined in to a single output.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                    | Value | Description              
 * :----------------------------------------|:------|:--------------------------
 *  ALT_I2C_COMP_PARAM_1_INTR_IO_E_COMBINED | 0x1   | Combined Interrupt Output
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_COMP_PARAM_1_INTR_IO
 * 
 * Combined Interrupt Output
 */
#define ALT_I2C_COMP_PARAM_1_INTR_IO_E_COMBINED 0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_COMP_PARAM_1_INTR_IO register field. */
#define ALT_I2C_COMP_PARAM_1_INTR_IO_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_I2C_COMP_PARAM_1_INTR_IO register field. */
#define ALT_I2C_COMP_PARAM_1_INTR_IO_MSB        5
/* The width in bits of the ALT_I2C_COMP_PARAM_1_INTR_IO register field. */
#define ALT_I2C_COMP_PARAM_1_INTR_IO_WIDTH      1
/* The mask used to set the ALT_I2C_COMP_PARAM_1_INTR_IO register field value. */
#define ALT_I2C_COMP_PARAM_1_INTR_IO_SET_MSK    0x00000020
/* The mask used to clear the ALT_I2C_COMP_PARAM_1_INTR_IO register field value. */
#define ALT_I2C_COMP_PARAM_1_INTR_IO_CLR_MSK    0xffffffdf
/* The reset value of the ALT_I2C_COMP_PARAM_1_INTR_IO register field. */
#define ALT_I2C_COMP_PARAM_1_INTR_IO_RESET      0x1
/* Extracts the ALT_I2C_COMP_PARAM_1_INTR_IO field value from a register. */
#define ALT_I2C_COMP_PARAM_1_INTR_IO_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_I2C_COMP_PARAM_1_INTR_IO register field value suitable for setting the register. */
#define ALT_I2C_COMP_PARAM_1_INTR_IO_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Has DMA - has_dma
 * 
 * This configures the inclusion of DMA handshaking interface signals.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description
 * :---------------------------------------|:------|:------------
 *  ALT_I2C_COMP_PARAM_1_HAS_DMA_E_PRESENT | 0x1   | Has DMA    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_COMP_PARAM_1_HAS_DMA
 * 
 * Has DMA
 */
#define ALT_I2C_COMP_PARAM_1_HAS_DMA_E_PRESENT  0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_COMP_PARAM_1_HAS_DMA register field. */
#define ALT_I2C_COMP_PARAM_1_HAS_DMA_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_I2C_COMP_PARAM_1_HAS_DMA register field. */
#define ALT_I2C_COMP_PARAM_1_HAS_DMA_MSB        6
/* The width in bits of the ALT_I2C_COMP_PARAM_1_HAS_DMA register field. */
#define ALT_I2C_COMP_PARAM_1_HAS_DMA_WIDTH      1
/* The mask used to set the ALT_I2C_COMP_PARAM_1_HAS_DMA register field value. */
#define ALT_I2C_COMP_PARAM_1_HAS_DMA_SET_MSK    0x00000040
/* The mask used to clear the ALT_I2C_COMP_PARAM_1_HAS_DMA register field value. */
#define ALT_I2C_COMP_PARAM_1_HAS_DMA_CLR_MSK    0xffffffbf
/* The reset value of the ALT_I2C_COMP_PARAM_1_HAS_DMA register field. */
#define ALT_I2C_COMP_PARAM_1_HAS_DMA_RESET      0x1
/* Extracts the ALT_I2C_COMP_PARAM_1_HAS_DMA field value from a register. */
#define ALT_I2C_COMP_PARAM_1_HAS_DMA_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_I2C_COMP_PARAM_1_HAS_DMA register field value suitable for setting the register. */
#define ALT_I2C_COMP_PARAM_1_HAS_DMA_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Add Encoded Params - add_encoded_params
 * 
 * By adding in the encoded parameters, this gives firmware an easy and quick way
 * of identifying the DesignWare component within an I/O memory map. Some critical
 * design-time options determine how a driver should interact with the peripheral.
 * There is a minimal area overhead by including these parameters. Allows a single
 * driver to be developed for each component which will be self-configurable.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                               | Value | Description       
 * :---------------------------------------------------|:------|:-------------------
 *  ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS_E_ADDENCPARAMS | 0x1   | Add Encoded Params
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS
 * 
 * Add Encoded Params
 */
#define ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS_E_ADDENCPARAMS  0x1

/* The Least Significant Bit (LSB) position of the ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS register field. */
#define ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS register field. */
#define ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS_MSB        7
/* The width in bits of the ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS register field. */
#define ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS_WIDTH      1
/* The mask used to set the ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS register field value. */
#define ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS_SET_MSK    0x00000080
/* The mask used to clear the ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS register field value. */
#define ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS_CLR_MSK    0xffffff7f
/* The reset value of the ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS register field. */
#define ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS_RESET      0x1
/* Extracts the ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS field value from a register. */
#define ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS register field value suitable for setting the register. */
#define ALT_I2C_COMP_PARAM_1_ADD_ENC_PARAMS_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Rx Buffer Depth - rx_buffer_depth
 * 
 * Sets Rx FIFO Depth.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                            | Value | Description             
 * :------------------------------------------------|:------|:-------------------------
 *  ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH_E_FIFO64BYTES | 0x40  | Rx Fifo Depth 64 Entries
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH
 * 
 * Rx Fifo Depth 64 Entries
 */
#define ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH_E_FIFO64BYTES 0x40

/* The Least Significant Bit (LSB) position of the ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH register field. */
#define ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH register field. */
#define ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH_MSB        15
/* The width in bits of the ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH register field. */
#define ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH_WIDTH      8
/* The mask used to set the ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH register field value. */
#define ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH_SET_MSK    0x0000ff00
/* The mask used to clear the ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH register field value. */
#define ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH_CLR_MSK    0xffff00ff
/* The reset value of the ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH register field. */
#define ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH_RESET      0x3f
/* Extracts the ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH field value from a register. */
#define ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH_GET(value) (((value) & 0x0000ff00) >> 8)
/* Produces a ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH register field value suitable for setting the register. */
#define ALT_I2C_COMP_PARAM_1_RX_BUF_DEPTH_SET(value) (((value) << 8) & 0x0000ff00)

/*
 * Field : Tx Buffer Depth - tx_buffer_depth
 * 
 * Sets Tx FIFO Depth.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                            | Value | Description               
 * :------------------------------------------------|:------|:---------------------------
 *  ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH_E_FIFO64BYTES | 0x40  | Tx Buffer Depth 64 Entries
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH
 * 
 * Tx Buffer Depth 64 Entries
 */
#define ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH_E_FIFO64BYTES 0x40

/* The Least Significant Bit (LSB) position of the ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH register field. */
#define ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH register field. */
#define ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH_MSB        23
/* The width in bits of the ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH register field. */
#define ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH_WIDTH      8
/* The mask used to set the ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH register field value. */
#define ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH_SET_MSK    0x00ff0000
/* The mask used to clear the ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH register field value. */
#define ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH_CLR_MSK    0xff00ffff
/* The reset value of the ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH register field. */
#define ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH_RESET      0x3f
/* Extracts the ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH field value from a register. */
#define ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH_GET(value) (((value) & 0x00ff0000) >> 16)
/* Produces a ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH register field value suitable for setting the register. */
#define ALT_I2C_COMP_PARAM_1_TX_BUF_DEPTH_SET(value) (((value) << 16) & 0x00ff0000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_COMP_PARAM_1.
 */
struct ALT_I2C_COMP_PARAM_1_s
{
    const uint32_t  apb_data_width     :  2;  /* APB Data Width Register */
    const uint32_t  max_speed_mode     :  2;  /* Max Speed Mode */
    const uint32_t  hc_count_values    :  1;  /* CNT Registers Access */
    const uint32_t  intr_io            :  1;  /* Intr IO */
    const uint32_t  has_dma            :  1;  /* Has DMA */
    const uint32_t  add_encoded_params :  1;  /* Add Encoded Params */
    const uint32_t  rx_buffer_depth    :  8;  /* Rx Buffer Depth */
    const uint32_t  tx_buffer_depth    :  8;  /* Tx Buffer Depth */
    uint32_t                           :  8;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_I2C_COMP_PARAM_1. */
typedef volatile struct ALT_I2C_COMP_PARAM_1_s  ALT_I2C_COMP_PARAM_1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_COMP_PARAM_1 register from the beginning of the component. */
#define ALT_I2C_COMP_PARAM_1_OFST        0xf4
/* The address of the ALT_I2C_COMP_PARAM_1 register. */
#define ALT_I2C_COMP_PARAM_1_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_COMP_PARAM_1_OFST))

/*
 * Register : Component Version Register - ic_comp_version
 * 
 * Describes the version of the I2C
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset      | Description              
 * :-------|:-------|:-----------|:--------------------------
 *  [31:0] | R      | 0x3132302a | Component Parameter Value
 * 
 */
/*
 * Field : Component Parameter Value - ic_comp_version
 * 
 * Specifies I2C release number (encoded as 4 ASCII characters)
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                     | Value      | Description  
 * :-----------------------------------------|:-----------|:--------------
 *  ALT_I2C_COMP_VER_IC_COMP_VER_E_VER_1_20A | 0x3132302a | Version 1.20a
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_I2C_COMP_VER_IC_COMP_VER
 * 
 * Version 1.20a
 */
#define ALT_I2C_COMP_VER_IC_COMP_VER_E_VER_1_20A    0x3132302a

/* The Least Significant Bit (LSB) position of the ALT_I2C_COMP_VER_IC_COMP_VER register field. */
#define ALT_I2C_COMP_VER_IC_COMP_VER_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_COMP_VER_IC_COMP_VER register field. */
#define ALT_I2C_COMP_VER_IC_COMP_VER_MSB        31
/* The width in bits of the ALT_I2C_COMP_VER_IC_COMP_VER register field. */
#define ALT_I2C_COMP_VER_IC_COMP_VER_WIDTH      32
/* The mask used to set the ALT_I2C_COMP_VER_IC_COMP_VER register field value. */
#define ALT_I2C_COMP_VER_IC_COMP_VER_SET_MSK    0xffffffff
/* The mask used to clear the ALT_I2C_COMP_VER_IC_COMP_VER register field value. */
#define ALT_I2C_COMP_VER_IC_COMP_VER_CLR_MSK    0x00000000
/* The reset value of the ALT_I2C_COMP_VER_IC_COMP_VER register field. */
#define ALT_I2C_COMP_VER_IC_COMP_VER_RESET      0x3132302a
/* Extracts the ALT_I2C_COMP_VER_IC_COMP_VER field value from a register. */
#define ALT_I2C_COMP_VER_IC_COMP_VER_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_I2C_COMP_VER_IC_COMP_VER register field value suitable for setting the register. */
#define ALT_I2C_COMP_VER_IC_COMP_VER_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_COMP_VER.
 */
struct ALT_I2C_COMP_VER_s
{
    const uint32_t  ic_comp_version : 32;  /* Component Parameter Value */
};

/* The typedef declaration for register ALT_I2C_COMP_VER. */
typedef volatile struct ALT_I2C_COMP_VER_s  ALT_I2C_COMP_VER_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_COMP_VER register from the beginning of the component. */
#define ALT_I2C_COMP_VER_OFST        0xf8
/* The address of the ALT_I2C_COMP_VER register. */
#define ALT_I2C_COMP_VER_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_COMP_VER_OFST))

/*
 * Register : Component Type Register - ic_comp_type
 * 
 * Describes a unique ASCII value
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset      | Description          
 * :-------|:-------|:-----------|:----------------------
 *  [31:0] | R      | 0x44570140 | Component Type Number
 * 
 */
/*
 * Field : Component Type Number - ic_comp_type
 * 
 * Designware Component Type number = 0x44_57_01_40. This assigned unique hex value
 * is constant and is derived from the two ASCII letters 'DW' followed by a 16-bit
 * unsigned number.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_I2C_COMP_TYPE_IC_COMP_TYPE register field. */
#define ALT_I2C_COMP_TYPE_IC_COMP_TYPE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_I2C_COMP_TYPE_IC_COMP_TYPE register field. */
#define ALT_I2C_COMP_TYPE_IC_COMP_TYPE_MSB        31
/* The width in bits of the ALT_I2C_COMP_TYPE_IC_COMP_TYPE register field. */
#define ALT_I2C_COMP_TYPE_IC_COMP_TYPE_WIDTH      32
/* The mask used to set the ALT_I2C_COMP_TYPE_IC_COMP_TYPE register field value. */
#define ALT_I2C_COMP_TYPE_IC_COMP_TYPE_SET_MSK    0xffffffff
/* The mask used to clear the ALT_I2C_COMP_TYPE_IC_COMP_TYPE register field value. */
#define ALT_I2C_COMP_TYPE_IC_COMP_TYPE_CLR_MSK    0x00000000
/* The reset value of the ALT_I2C_COMP_TYPE_IC_COMP_TYPE register field. */
#define ALT_I2C_COMP_TYPE_IC_COMP_TYPE_RESET      0x44570140
/* Extracts the ALT_I2C_COMP_TYPE_IC_COMP_TYPE field value from a register. */
#define ALT_I2C_COMP_TYPE_IC_COMP_TYPE_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_I2C_COMP_TYPE_IC_COMP_TYPE register field value suitable for setting the register. */
#define ALT_I2C_COMP_TYPE_IC_COMP_TYPE_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_I2C_COMP_TYPE.
 */
struct ALT_I2C_COMP_TYPE_s
{
    const uint32_t  ic_comp_type : 32;  /* Component Type Number */
};

/* The typedef declaration for register ALT_I2C_COMP_TYPE. */
typedef volatile struct ALT_I2C_COMP_TYPE_s  ALT_I2C_COMP_TYPE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_I2C_COMP_TYPE register from the beginning of the component. */
#define ALT_I2C_COMP_TYPE_OFST        0xfc
/* The address of the ALT_I2C_COMP_TYPE register. */
#define ALT_I2C_COMP_TYPE_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_I2C_COMP_TYPE_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_I2C.
 */
struct ALT_I2C_s
{
    volatile ALT_I2C_CON_t                 ic_con;                 /* ALT_I2C_CON */
    volatile ALT_I2C_TAR_t                 ic_tar;                 /* ALT_I2C_TAR */
    volatile ALT_I2C_SAR_t                 ic_sar;                 /* ALT_I2C_SAR */
    volatile uint32_t                      _pad_0xc_0xf;           /* *UNDEFINED* */
    volatile ALT_I2C_DATA_CMD_t            ic_data_cmd;            /* ALT_I2C_DATA_CMD */
    volatile ALT_I2C_SS_SCL_HCNT_t         ic_ss_scl_hcnt;         /* ALT_I2C_SS_SCL_HCNT */
    volatile ALT_I2C_SS_SCL_LCNT_t         ic_ss_scl_lcnt;         /* ALT_I2C_SS_SCL_LCNT */
    volatile ALT_I2C_FS_SCL_HCNT_t         ic_fs_scl_hcnt;         /* ALT_I2C_FS_SCL_HCNT */
    volatile ALT_I2C_FS_SCL_LCNT_t         ic_fs_scl_lcnt;         /* ALT_I2C_FS_SCL_LCNT */
    volatile uint32_t                      _pad_0x24_0x2b[2];      /* *UNDEFINED* */
    volatile ALT_I2C_INTR_STAT_t           ic_intr_stat;           /* ALT_I2C_INTR_STAT */
    volatile ALT_I2C_INTR_MSK_t            ic_intr_mask;           /* ALT_I2C_INTR_MSK */
    volatile ALT_I2C_RAW_INTR_STAT_t       ic_raw_intr_stat;       /* ALT_I2C_RAW_INTR_STAT */
    volatile ALT_I2C_RX_TL_t               ic_rx_tl;               /* ALT_I2C_RX_TL */
    volatile ALT_I2C_TX_TL_t               ic_tx_tl;               /* ALT_I2C_TX_TL */
    volatile ALT_I2C_CLR_INTR_t            ic_clr_intr;            /* ALT_I2C_CLR_INTR */
    volatile ALT_I2C_CLR_RX_UNDER_t        ic_clr_rx_under;        /* ALT_I2C_CLR_RX_UNDER */
    volatile ALT_I2C_CLR_RX_OVER_t         ic_clr_rx_over;         /* ALT_I2C_CLR_RX_OVER */
    volatile ALT_I2C_CLR_TX_OVER_t         ic_clr_tx_over;         /* ALT_I2C_CLR_TX_OVER */
    volatile ALT_I2C_CLR_RD_REQ_t          ic_clr_rd_req;          /* ALT_I2C_CLR_RD_REQ */
    volatile ALT_I2C_CLR_TX_ABRT_t         ic_clr_tx_abrt;         /* ALT_I2C_CLR_TX_ABRT */
    volatile ALT_I2C_CLR_RX_DONE_t         ic_clr_rx_done;         /* ALT_I2C_CLR_RX_DONE */
    volatile ALT_I2C_CLR_ACTIVITY_t        ic_clr_activity;        /* ALT_I2C_CLR_ACTIVITY */
    volatile ALT_I2C_CLR_STOP_DET_t        ic_clr_stop_det;        /* ALT_I2C_CLR_STOP_DET */
    volatile ALT_I2C_CLR_START_DET_t       ic_clr_start_det;       /* ALT_I2C_CLR_START_DET */
    volatile ALT_I2C_CLR_GEN_CALL_t        ic_clr_gen_call;        /* ALT_I2C_CLR_GEN_CALL */
    volatile ALT_I2C_EN_t                  ic_enable;              /* ALT_I2C_EN */
    volatile ALT_I2C_STAT_t                ic_status;              /* ALT_I2C_STAT */
    volatile ALT_I2C_TXFLR_t               ic_txflr;               /* ALT_I2C_TXFLR */
    volatile ALT_I2C_RXFLR_t               ic_rxflr;               /* ALT_I2C_RXFLR */
    volatile ALT_I2C_SDA_HOLD_t            ic_sda_hold;            /* ALT_I2C_SDA_HOLD */
    volatile ALT_I2C_TX_ABRT_SRC_t         ic_tx_abrt_source;      /* ALT_I2C_TX_ABRT_SRC */
    volatile ALT_I2C_SLV_DATA_NACK_ONLY_t  ic_slv_data_nack_only;  /* ALT_I2C_SLV_DATA_NACK_ONLY */
    volatile ALT_I2C_DMA_CR_t              ic_dma_cr;              /* ALT_I2C_DMA_CR */
    volatile ALT_I2C_DMA_TDLR_t            ic_dma_tdlr;            /* ALT_I2C_DMA_TDLR */
    volatile ALT_I2C_DMA_RDLR_t            ic_dma_rdlr;            /* ALT_I2C_DMA_RDLR */
    volatile ALT_I2C_SDA_SETUP_t           ic_sda_setup;           /* ALT_I2C_SDA_SETUP */
    volatile ALT_I2C_ACK_GENERAL_CALL_t    ic_ack_general_call;    /* ALT_I2C_ACK_GENERAL_CALL */
    volatile ALT_I2C_EN_STAT_t             ic_enable_status;       /* ALT_I2C_EN_STAT */
    volatile ALT_I2C_FS_SPKLEN_t           ic_fs_spklen;           /* ALT_I2C_FS_SPKLEN */
    volatile uint32_t                      _pad_0xa4_0xf3[20];     /* *UNDEFINED* */
    volatile ALT_I2C_COMP_PARAM_1_t        ic_comp_param_1;        /* ALT_I2C_COMP_PARAM_1 */
    volatile ALT_I2C_COMP_VER_t            ic_comp_version;        /* ALT_I2C_COMP_VER */
    volatile ALT_I2C_COMP_TYPE_t           ic_comp_type;           /* ALT_I2C_COMP_TYPE */
};

/* The typedef declaration for register group ALT_I2C. */
typedef volatile struct ALT_I2C_s  ALT_I2C_t;
/* The struct declaration for the raw register contents of register group ALT_I2C. */
struct ALT_I2C_raw_s
{
    volatile uint32_t  ic_con;                 /* ALT_I2C_CON */
    volatile uint32_t  ic_tar;                 /* ALT_I2C_TAR */
    volatile uint32_t  ic_sar;                 /* ALT_I2C_SAR */
    volatile uint32_t  _pad_0xc_0xf;           /* *UNDEFINED* */
    volatile uint32_t  ic_data_cmd;            /* ALT_I2C_DATA_CMD */
    volatile uint32_t  ic_ss_scl_hcnt;         /* ALT_I2C_SS_SCL_HCNT */
    volatile uint32_t  ic_ss_scl_lcnt;         /* ALT_I2C_SS_SCL_LCNT */
    volatile uint32_t  ic_fs_scl_hcnt;         /* ALT_I2C_FS_SCL_HCNT */
    volatile uint32_t  ic_fs_scl_lcnt;         /* ALT_I2C_FS_SCL_LCNT */
    volatile uint32_t  _pad_0x24_0x2b[2];      /* *UNDEFINED* */
    volatile uint32_t  ic_intr_stat;           /* ALT_I2C_INTR_STAT */
    volatile uint32_t  ic_intr_mask;           /* ALT_I2C_INTR_MSK */
    volatile uint32_t  ic_raw_intr_stat;       /* ALT_I2C_RAW_INTR_STAT */
    volatile uint32_t  ic_rx_tl;               /* ALT_I2C_RX_TL */
    volatile uint32_t  ic_tx_tl;               /* ALT_I2C_TX_TL */
    volatile uint32_t  ic_clr_intr;            /* ALT_I2C_CLR_INTR */
    volatile uint32_t  ic_clr_rx_under;        /* ALT_I2C_CLR_RX_UNDER */
    volatile uint32_t  ic_clr_rx_over;         /* ALT_I2C_CLR_RX_OVER */
    volatile uint32_t  ic_clr_tx_over;         /* ALT_I2C_CLR_TX_OVER */
    volatile uint32_t  ic_clr_rd_req;          /* ALT_I2C_CLR_RD_REQ */
    volatile uint32_t  ic_clr_tx_abrt;         /* ALT_I2C_CLR_TX_ABRT */
    volatile uint32_t  ic_clr_rx_done;         /* ALT_I2C_CLR_RX_DONE */
    volatile uint32_t  ic_clr_activity;        /* ALT_I2C_CLR_ACTIVITY */
    volatile uint32_t  ic_clr_stop_det;        /* ALT_I2C_CLR_STOP_DET */
    volatile uint32_t  ic_clr_start_det;       /* ALT_I2C_CLR_START_DET */
    volatile uint32_t  ic_clr_gen_call;        /* ALT_I2C_CLR_GEN_CALL */
    volatile uint32_t  ic_enable;              /* ALT_I2C_EN */
    volatile uint32_t  ic_status;              /* ALT_I2C_STAT */
    volatile uint32_t  ic_txflr;               /* ALT_I2C_TXFLR */
    volatile uint32_t  ic_rxflr;               /* ALT_I2C_RXFLR */
    volatile uint32_t  ic_sda_hold;            /* ALT_I2C_SDA_HOLD */
    volatile uint32_t  ic_tx_abrt_source;      /* ALT_I2C_TX_ABRT_SRC */
    volatile uint32_t  ic_slv_data_nack_only;  /* ALT_I2C_SLV_DATA_NACK_ONLY */
    volatile uint32_t  ic_dma_cr;              /* ALT_I2C_DMA_CR */
    volatile uint32_t  ic_dma_tdlr;            /* ALT_I2C_DMA_TDLR */
    volatile uint32_t  ic_dma_rdlr;            /* ALT_I2C_DMA_RDLR */
    volatile uint32_t  ic_sda_setup;           /* ALT_I2C_SDA_SETUP */
    volatile uint32_t  ic_ack_general_call;    /* ALT_I2C_ACK_GENERAL_CALL */
    volatile uint32_t  ic_enable_status;       /* ALT_I2C_EN_STAT */
    volatile uint32_t  ic_fs_spklen;           /* ALT_I2C_FS_SPKLEN */
    volatile uint32_t  _pad_0xa4_0xf3[20];     /* *UNDEFINED* */
    volatile uint32_t  ic_comp_param_1;        /* ALT_I2C_COMP_PARAM_1 */
    volatile uint32_t  ic_comp_version;        /* ALT_I2C_COMP_VER */
    volatile uint32_t  ic_comp_type;           /* ALT_I2C_COMP_TYPE */
};

/* The typedef declaration for the raw register contents of register group ALT_I2C. */
typedef volatile struct ALT_I2C_raw_s  ALT_I2C_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_I2C_H__ */

