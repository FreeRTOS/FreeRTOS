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

/* Altera - ALT_SDR */

#ifndef __ALTERA_ALT_SDR_H__
#define __ALTERA_ALT_SDR_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : SDRAM Controller - ALT_SDR
 * SDRAM Controller
 * 
 * Address map for the SDRAM Interface registers
 * 
 */
/*
 * Register Group : SDRAM Controller Module - ALT_SDR_CTL
 * SDRAM Controller Module
 * 
 * Address map for the SDRAM controller and multi-port front-end.
 * 
 * All registers in this group reset to zero.
 * 
 */
/*
 * Register : Controller Configuration Register - ctrlcfg
 * 
 * The Controller Configuration Register determines the behavior of the controller.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description               
 * :--------|:-------|:--------|:---------------------------
 *  [2:0]   | RW     | Unknown | DRAM Memory Type          
 *  [7:3]   | RW     | Unknown | DRAM Memory Burst Length  
 *  [9:8]   | RW     | Unknown | Address Interleaving Order
 *  [10]    | RW     | Unknown | ECC Enable                
 *  [11]    | RW     | Unknown | ECC Auto-Correction Enable
 *  [12]    | RW     | Unknown | TBD                       
 *  [13]    | RW     | Unknown | Generate Single Bit Errors
 *  [14]    | RW     | Unknown | Generate Double Bit Errors
 *  [15]    | RW     | Unknown | Command Reorder Enable    
 *  [21:16] | RW     | Unknown | Starvation Limit          
 *  [22]    | RW     | Unknown | DQS Tracking Enable       
 *  [23]    | RW     | Unknown | No DM Pins Present        
 *  [24]    | RW     | Unknown | Burst Interrupt Enable    
 *  [25]    | RW     | Unknown | Burst Terminate Enable    
 *  [31:26] | ???    | Unknown | *UNDEFINED*               
 * 
 */
/*
 * Field : DRAM Memory Type - memtype
 * 
 * Selects memory type. Program this field with one of the following binary values,
 * &quot;001&quot; for DDR2 SDRAM, &quot;010&quot; for DDR3 SDRAM, &quot;011&quot;
 * for LPDDR1 SDRAM or &quot;100&quot; for LPDDR2 SDRAM.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLCFG_MEMTYPE register field. */
#define ALT_SDR_CTL_CTLCFG_MEMTYPE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLCFG_MEMTYPE register field. */
#define ALT_SDR_CTL_CTLCFG_MEMTYPE_MSB        2
/* The width in bits of the ALT_SDR_CTL_CTLCFG_MEMTYPE register field. */
#define ALT_SDR_CTL_CTLCFG_MEMTYPE_WIDTH      3
/* The mask used to set the ALT_SDR_CTL_CTLCFG_MEMTYPE register field value. */
#define ALT_SDR_CTL_CTLCFG_MEMTYPE_SET_MSK    0x00000007
/* The mask used to clear the ALT_SDR_CTL_CTLCFG_MEMTYPE register field value. */
#define ALT_SDR_CTL_CTLCFG_MEMTYPE_CLR_MSK    0xfffffff8
/* The reset value of the ALT_SDR_CTL_CTLCFG_MEMTYPE register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLCFG_MEMTYPE_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLCFG_MEMTYPE field value from a register. */
#define ALT_SDR_CTL_CTLCFG_MEMTYPE_GET(value) (((value) & 0x00000007) >> 0)
/* Produces a ALT_SDR_CTL_CTLCFG_MEMTYPE register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLCFG_MEMTYPE_SET(value) (((value) << 0) & 0x00000007)

/*
 * Field : DRAM Memory Burst Length - membl
 * 
 * Configures burst length as a static decimal value.  Legal values are valid for
 * JEDEC allowed DRAM values for the DRAM selected in cfg_type.  For DDR3, this
 * should be programmed with 8 (binary &quot;01000&quot;), for DDR2 it can be
 * either 4 or 8 depending on the exact DRAM chip.  LPDDR2 can be programmed with
 * 4, 8, or 16 and LPDDR can be programmed with 2, 4, or 8. You must also program
 * the membl field in the staticcfg register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLCFG_MEMBL register field. */
#define ALT_SDR_CTL_CTLCFG_MEMBL_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLCFG_MEMBL register field. */
#define ALT_SDR_CTL_CTLCFG_MEMBL_MSB        7
/* The width in bits of the ALT_SDR_CTL_CTLCFG_MEMBL register field. */
#define ALT_SDR_CTL_CTLCFG_MEMBL_WIDTH      5
/* The mask used to set the ALT_SDR_CTL_CTLCFG_MEMBL register field value. */
#define ALT_SDR_CTL_CTLCFG_MEMBL_SET_MSK    0x000000f8
/* The mask used to clear the ALT_SDR_CTL_CTLCFG_MEMBL register field value. */
#define ALT_SDR_CTL_CTLCFG_MEMBL_CLR_MSK    0xffffff07
/* The reset value of the ALT_SDR_CTL_CTLCFG_MEMBL register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLCFG_MEMBL_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLCFG_MEMBL field value from a register. */
#define ALT_SDR_CTL_CTLCFG_MEMBL_GET(value) (((value) & 0x000000f8) >> 3)
/* Produces a ALT_SDR_CTL_CTLCFG_MEMBL register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLCFG_MEMBL_SET(value) (((value) << 3) & 0x000000f8)

/*
 * Field : Address Interleaving Order - addrorder
 * 
 * Selects the order for address interleaving.  Programming this field with
 * different values gives different mappings between the AXI or Avalon-MM address
 * and the SDRAM address. Program this field with the following binary values to
 * select the ordering. &quot;00&quot; - chip, row, bank, column, &quot;01&quot; -
 * chip, bank, row, column, &quot;10&quot;-row, chip, bank, column
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLCFG_ADDRORDER register field. */
#define ALT_SDR_CTL_CTLCFG_ADDRORDER_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLCFG_ADDRORDER register field. */
#define ALT_SDR_CTL_CTLCFG_ADDRORDER_MSB        9
/* The width in bits of the ALT_SDR_CTL_CTLCFG_ADDRORDER register field. */
#define ALT_SDR_CTL_CTLCFG_ADDRORDER_WIDTH      2
/* The mask used to set the ALT_SDR_CTL_CTLCFG_ADDRORDER register field value. */
#define ALT_SDR_CTL_CTLCFG_ADDRORDER_SET_MSK    0x00000300
/* The mask used to clear the ALT_SDR_CTL_CTLCFG_ADDRORDER register field value. */
#define ALT_SDR_CTL_CTLCFG_ADDRORDER_CLR_MSK    0xfffffcff
/* The reset value of the ALT_SDR_CTL_CTLCFG_ADDRORDER register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLCFG_ADDRORDER_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLCFG_ADDRORDER field value from a register. */
#define ALT_SDR_CTL_CTLCFG_ADDRORDER_GET(value) (((value) & 0x00000300) >> 8)
/* Produces a ALT_SDR_CTL_CTLCFG_ADDRORDER register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLCFG_ADDRORDER_SET(value) (((value) << 8) & 0x00000300)

/*
 * Field : ECC Enable - eccen
 * 
 * Enable the generation and checking of ECC.  This bit must only be set if the
 * memory connected to the SDRAM interface is 24 or 40 bits wide. If you set this,
 * you must clear the useeccasdata field in the staticcfg register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLCFG_ECCEN register field. */
#define ALT_SDR_CTL_CTLCFG_ECCEN_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLCFG_ECCEN register field. */
#define ALT_SDR_CTL_CTLCFG_ECCEN_MSB        10
/* The width in bits of the ALT_SDR_CTL_CTLCFG_ECCEN register field. */
#define ALT_SDR_CTL_CTLCFG_ECCEN_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_CTLCFG_ECCEN register field value. */
#define ALT_SDR_CTL_CTLCFG_ECCEN_SET_MSK    0x00000400
/* The mask used to clear the ALT_SDR_CTL_CTLCFG_ECCEN register field value. */
#define ALT_SDR_CTL_CTLCFG_ECCEN_CLR_MSK    0xfffffbff
/* The reset value of the ALT_SDR_CTL_CTLCFG_ECCEN register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLCFG_ECCEN_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLCFG_ECCEN field value from a register. */
#define ALT_SDR_CTL_CTLCFG_ECCEN_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_SDR_CTL_CTLCFG_ECCEN register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLCFG_ECCEN_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : ECC Auto-Correction Enable - ecccorren
 * 
 * Enable auto correction of the read data returned when single bit error is
 * detected.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLCFG_ECCCORREN register field. */
#define ALT_SDR_CTL_CTLCFG_ECCCORREN_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLCFG_ECCCORREN register field. */
#define ALT_SDR_CTL_CTLCFG_ECCCORREN_MSB        11
/* The width in bits of the ALT_SDR_CTL_CTLCFG_ECCCORREN register field. */
#define ALT_SDR_CTL_CTLCFG_ECCCORREN_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_CTLCFG_ECCCORREN register field value. */
#define ALT_SDR_CTL_CTLCFG_ECCCORREN_SET_MSK    0x00000800
/* The mask used to clear the ALT_SDR_CTL_CTLCFG_ECCCORREN register field value. */
#define ALT_SDR_CTL_CTLCFG_ECCCORREN_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_SDR_CTL_CTLCFG_ECCCORREN register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLCFG_ECCCORREN_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLCFG_ECCCORREN field value from a register. */
#define ALT_SDR_CTL_CTLCFG_ECCCORREN_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_SDR_CTL_CTLCFG_ECCCORREN register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLCFG_ECCCORREN_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : TBD - cfg_enable_ecc_code_overwrites
 * 
 * Set to a one to enable ECC overwrites.  ECC overwrites occur when a correctable
 * ECC error is seen and cause a new read/modify/write to be scheduled for that
 * location to clear the ECC error.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS register field. */
#define ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS register field. */
#define ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS_MSB        12
/* The width in bits of the ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS register field. */
#define ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS register field value. */
#define ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS_SET_MSK    0x00001000
/* The mask used to clear the ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS register field value. */
#define ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS_CLR_MSK    0xffffefff
/* The reset value of the ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS field value from a register. */
#define ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLCFG_CFG_EN_ECC_CODE_OVERWRS_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : Generate Single Bit Errors - gensbe
 * 
 * Enable the deliberate insertion of single bit errors in data written to memory.
 * This should only be used for testing purposes.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLCFG_GENSBE register field. */
#define ALT_SDR_CTL_CTLCFG_GENSBE_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLCFG_GENSBE register field. */
#define ALT_SDR_CTL_CTLCFG_GENSBE_MSB        13
/* The width in bits of the ALT_SDR_CTL_CTLCFG_GENSBE register field. */
#define ALT_SDR_CTL_CTLCFG_GENSBE_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_CTLCFG_GENSBE register field value. */
#define ALT_SDR_CTL_CTLCFG_GENSBE_SET_MSK    0x00002000
/* The mask used to clear the ALT_SDR_CTL_CTLCFG_GENSBE register field value. */
#define ALT_SDR_CTL_CTLCFG_GENSBE_CLR_MSK    0xffffdfff
/* The reset value of the ALT_SDR_CTL_CTLCFG_GENSBE register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLCFG_GENSBE_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLCFG_GENSBE field value from a register. */
#define ALT_SDR_CTL_CTLCFG_GENSBE_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_SDR_CTL_CTLCFG_GENSBE register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLCFG_GENSBE_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : Generate Double Bit Errors - gendbe
 * 
 * Enable the deliberate insertion of double bit errors in data written to memory.
 * This should only be used for testing purposes.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLCFG_GENDBE register field. */
#define ALT_SDR_CTL_CTLCFG_GENDBE_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLCFG_GENDBE register field. */
#define ALT_SDR_CTL_CTLCFG_GENDBE_MSB        14
/* The width in bits of the ALT_SDR_CTL_CTLCFG_GENDBE register field. */
#define ALT_SDR_CTL_CTLCFG_GENDBE_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_CTLCFG_GENDBE register field value. */
#define ALT_SDR_CTL_CTLCFG_GENDBE_SET_MSK    0x00004000
/* The mask used to clear the ALT_SDR_CTL_CTLCFG_GENDBE register field value. */
#define ALT_SDR_CTL_CTLCFG_GENDBE_CLR_MSK    0xffffbfff
/* The reset value of the ALT_SDR_CTL_CTLCFG_GENDBE register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLCFG_GENDBE_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLCFG_GENDBE field value from a register. */
#define ALT_SDR_CTL_CTLCFG_GENDBE_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_SDR_CTL_CTLCFG_GENDBE register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLCFG_GENDBE_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : Command Reorder Enable - reorderen
 * 
 * This bit controls whether the controller can re-order operations to optimize
 * SDRAM bandwidth.  It should generally be set to a one.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLCFG_REORDEREN register field. */
#define ALT_SDR_CTL_CTLCFG_REORDEREN_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLCFG_REORDEREN register field. */
#define ALT_SDR_CTL_CTLCFG_REORDEREN_MSB        15
/* The width in bits of the ALT_SDR_CTL_CTLCFG_REORDEREN register field. */
#define ALT_SDR_CTL_CTLCFG_REORDEREN_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_CTLCFG_REORDEREN register field value. */
#define ALT_SDR_CTL_CTLCFG_REORDEREN_SET_MSK    0x00008000
/* The mask used to clear the ALT_SDR_CTL_CTLCFG_REORDEREN register field value. */
#define ALT_SDR_CTL_CTLCFG_REORDEREN_CLR_MSK    0xffff7fff
/* The reset value of the ALT_SDR_CTL_CTLCFG_REORDEREN register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLCFG_REORDEREN_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLCFG_REORDEREN field value from a register. */
#define ALT_SDR_CTL_CTLCFG_REORDEREN_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_SDR_CTL_CTLCFG_REORDEREN register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLCFG_REORDEREN_SET(value) (((value) << 15) & 0x00008000)

/*
 * Field : Starvation Limit - starvelimit
 * 
 * Specifies the number of DRAM burst transactions an individual transaction will
 * allow to reorder ahead of it before its priority is raised in the memory
 * controller.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLCFG_STARVELIMIT register field. */
#define ALT_SDR_CTL_CTLCFG_STARVELIMIT_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLCFG_STARVELIMIT register field. */
#define ALT_SDR_CTL_CTLCFG_STARVELIMIT_MSB        21
/* The width in bits of the ALT_SDR_CTL_CTLCFG_STARVELIMIT register field. */
#define ALT_SDR_CTL_CTLCFG_STARVELIMIT_WIDTH      6
/* The mask used to set the ALT_SDR_CTL_CTLCFG_STARVELIMIT register field value. */
#define ALT_SDR_CTL_CTLCFG_STARVELIMIT_SET_MSK    0x003f0000
/* The mask used to clear the ALT_SDR_CTL_CTLCFG_STARVELIMIT register field value. */
#define ALT_SDR_CTL_CTLCFG_STARVELIMIT_CLR_MSK    0xffc0ffff
/* The reset value of the ALT_SDR_CTL_CTLCFG_STARVELIMIT register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLCFG_STARVELIMIT_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLCFG_STARVELIMIT field value from a register. */
#define ALT_SDR_CTL_CTLCFG_STARVELIMIT_GET(value) (((value) & 0x003f0000) >> 16)
/* Produces a ALT_SDR_CTL_CTLCFG_STARVELIMIT register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLCFG_STARVELIMIT_SET(value) (((value) << 16) & 0x003f0000)

/*
 * Field : DQS Tracking Enable - dqstrken
 * 
 * Enables DQS tracking in the PHY.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLCFG_DQSTRKEN register field. */
#define ALT_SDR_CTL_CTLCFG_DQSTRKEN_LSB        22
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLCFG_DQSTRKEN register field. */
#define ALT_SDR_CTL_CTLCFG_DQSTRKEN_MSB        22
/* The width in bits of the ALT_SDR_CTL_CTLCFG_DQSTRKEN register field. */
#define ALT_SDR_CTL_CTLCFG_DQSTRKEN_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_CTLCFG_DQSTRKEN register field value. */
#define ALT_SDR_CTL_CTLCFG_DQSTRKEN_SET_MSK    0x00400000
/* The mask used to clear the ALT_SDR_CTL_CTLCFG_DQSTRKEN register field value. */
#define ALT_SDR_CTL_CTLCFG_DQSTRKEN_CLR_MSK    0xffbfffff
/* The reset value of the ALT_SDR_CTL_CTLCFG_DQSTRKEN register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLCFG_DQSTRKEN_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLCFG_DQSTRKEN field value from a register. */
#define ALT_SDR_CTL_CTLCFG_DQSTRKEN_GET(value) (((value) & 0x00400000) >> 22)
/* Produces a ALT_SDR_CTL_CTLCFG_DQSTRKEN register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLCFG_DQSTRKEN_SET(value) (((value) << 22) & 0x00400000)

/*
 * Field : No DM Pins Present - nodmpins
 * 
 * Set to a one to enable DRAM operation if no DM pins are connected.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLCFG_NODMPINS register field. */
#define ALT_SDR_CTL_CTLCFG_NODMPINS_LSB        23
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLCFG_NODMPINS register field. */
#define ALT_SDR_CTL_CTLCFG_NODMPINS_MSB        23
/* The width in bits of the ALT_SDR_CTL_CTLCFG_NODMPINS register field. */
#define ALT_SDR_CTL_CTLCFG_NODMPINS_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_CTLCFG_NODMPINS register field value. */
#define ALT_SDR_CTL_CTLCFG_NODMPINS_SET_MSK    0x00800000
/* The mask used to clear the ALT_SDR_CTL_CTLCFG_NODMPINS register field value. */
#define ALT_SDR_CTL_CTLCFG_NODMPINS_CLR_MSK    0xff7fffff
/* The reset value of the ALT_SDR_CTL_CTLCFG_NODMPINS register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLCFG_NODMPINS_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLCFG_NODMPINS field value from a register. */
#define ALT_SDR_CTL_CTLCFG_NODMPINS_GET(value) (((value) & 0x00800000) >> 23)
/* Produces a ALT_SDR_CTL_CTLCFG_NODMPINS register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLCFG_NODMPINS_SET(value) (((value) << 23) & 0x00800000)

/*
 * Field : Burst Interrupt Enable - burstintren
 * 
 * Set to a one to enable the controller to issue burst interrupt commands. This
 * must only be set when the DRAM memory type is LPDDR2.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLCFG_BURSTINTREN register field. */
#define ALT_SDR_CTL_CTLCFG_BURSTINTREN_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLCFG_BURSTINTREN register field. */
#define ALT_SDR_CTL_CTLCFG_BURSTINTREN_MSB        24
/* The width in bits of the ALT_SDR_CTL_CTLCFG_BURSTINTREN register field. */
#define ALT_SDR_CTL_CTLCFG_BURSTINTREN_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_CTLCFG_BURSTINTREN register field value. */
#define ALT_SDR_CTL_CTLCFG_BURSTINTREN_SET_MSK    0x01000000
/* The mask used to clear the ALT_SDR_CTL_CTLCFG_BURSTINTREN register field value. */
#define ALT_SDR_CTL_CTLCFG_BURSTINTREN_CLR_MSK    0xfeffffff
/* The reset value of the ALT_SDR_CTL_CTLCFG_BURSTINTREN register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLCFG_BURSTINTREN_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLCFG_BURSTINTREN field value from a register. */
#define ALT_SDR_CTL_CTLCFG_BURSTINTREN_GET(value) (((value) & 0x01000000) >> 24)
/* Produces a ALT_SDR_CTL_CTLCFG_BURSTINTREN register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLCFG_BURSTINTREN_SET(value) (((value) << 24) & 0x01000000)

/*
 * Field : Burst Terminate Enable - bursttermen
 * 
 * Set to a one to enable the controller to issue burst terminate commands. This
 * must only be set when the DRAM memory type is LPDDR2.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLCFG_BURSTTERMEN register field. */
#define ALT_SDR_CTL_CTLCFG_BURSTTERMEN_LSB        25
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLCFG_BURSTTERMEN register field. */
#define ALT_SDR_CTL_CTLCFG_BURSTTERMEN_MSB        25
/* The width in bits of the ALT_SDR_CTL_CTLCFG_BURSTTERMEN register field. */
#define ALT_SDR_CTL_CTLCFG_BURSTTERMEN_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_CTLCFG_BURSTTERMEN register field value. */
#define ALT_SDR_CTL_CTLCFG_BURSTTERMEN_SET_MSK    0x02000000
/* The mask used to clear the ALT_SDR_CTL_CTLCFG_BURSTTERMEN register field value. */
#define ALT_SDR_CTL_CTLCFG_BURSTTERMEN_CLR_MSK    0xfdffffff
/* The reset value of the ALT_SDR_CTL_CTLCFG_BURSTTERMEN register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLCFG_BURSTTERMEN_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLCFG_BURSTTERMEN field value from a register. */
#define ALT_SDR_CTL_CTLCFG_BURSTTERMEN_GET(value) (((value) & 0x02000000) >> 25)
/* Produces a ALT_SDR_CTL_CTLCFG_BURSTTERMEN register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLCFG_BURSTTERMEN_SET(value) (((value) << 25) & 0x02000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_CTLCFG.
 */
struct ALT_SDR_CTL_CTLCFG_s
{
    uint32_t  memtype                        :  3;  /* DRAM Memory Type */
    uint32_t  membl                          :  5;  /* DRAM Memory Burst Length */
    uint32_t  addrorder                      :  2;  /* Address Interleaving Order */
    uint32_t  eccen                          :  1;  /* ECC Enable */
    uint32_t  ecccorren                      :  1;  /* ECC Auto-Correction Enable */
    uint32_t  cfg_enable_ecc_code_overwrites :  1;  /* TBD */
    uint32_t  gensbe                         :  1;  /* Generate Single Bit Errors */
    uint32_t  gendbe                         :  1;  /* Generate Double Bit Errors */
    uint32_t  reorderen                      :  1;  /* Command Reorder Enable */
    uint32_t  starvelimit                    :  6;  /* Starvation Limit */
    uint32_t  dqstrken                       :  1;  /* DQS Tracking Enable */
    uint32_t  nodmpins                       :  1;  /* No DM Pins Present */
    uint32_t  burstintren                    :  1;  /* Burst Interrupt Enable */
    uint32_t  bursttermen                    :  1;  /* Burst Terminate Enable */
    uint32_t                                 :  6;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_CTLCFG. */
typedef volatile struct ALT_SDR_CTL_CTLCFG_s  ALT_SDR_CTL_CTLCFG_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_CTLCFG register from the beginning of the component. */
#define ALT_SDR_CTL_CTLCFG_OFST        0x0

/*
 * Register : DRAM Timings 1 Register - dramtiming1
 * 
 * This register implements JEDEC standardized timing parameters.  It should be
 * programmed in clock cycles, for the value specified by the memory vendor.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description               
 * :--------|:-------|:--------|:---------------------------
 *  [3:0]   | RW     | Unknown | CAS Write Latency         
 *  [8:4]   | RW     | Unknown | Additive Latency          
 *  [13:9]  | RW     | Unknown | CAS Read Latency          
 *  [17:14] | RW     | Unknown | Activate to Activate Delay
 *  [23:18] | RW     | Unknown | Four Activate Window Time 
 *  [31:24] | RW     | Unknown | Refresh Cycle Time        
 * 
 */
/*
 * Field : CAS Write Latency - tcwl
 * 
 * Memory write latency.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING1_TCWL register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TCWL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING1_TCWL register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TCWL_MSB        3
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING1_TCWL register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TCWL_WIDTH      4
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING1_TCWL register field value. */
#define ALT_SDR_CTL_DRAMTIMING1_TCWL_SET_MSK    0x0000000f
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING1_TCWL register field value. */
#define ALT_SDR_CTL_DRAMTIMING1_TCWL_CLR_MSK    0xfffffff0
/* The reset value of the ALT_SDR_CTL_DRAMTIMING1_TCWL register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING1_TCWL_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING1_TCWL field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING1_TCWL_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_SDR_CTL_DRAMTIMING1_TCWL register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING1_TCWL_SET(value) (((value) << 0) & 0x0000000f)

/*
 * Field : Additive Latency - tal
 * 
 * Memory additive latency.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING1_TAL register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TAL_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING1_TAL register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TAL_MSB        8
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING1_TAL register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TAL_WIDTH      5
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING1_TAL register field value. */
#define ALT_SDR_CTL_DRAMTIMING1_TAL_SET_MSK    0x000001f0
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING1_TAL register field value. */
#define ALT_SDR_CTL_DRAMTIMING1_TAL_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_SDR_CTL_DRAMTIMING1_TAL register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING1_TAL_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING1_TAL field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING1_TAL_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_SDR_CTL_DRAMTIMING1_TAL register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING1_TAL_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : CAS Read Latency - tcl
 * 
 * Memory read latency.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING1_TCL register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TCL_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING1_TCL register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TCL_MSB        13
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING1_TCL register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TCL_WIDTH      5
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING1_TCL register field value. */
#define ALT_SDR_CTL_DRAMTIMING1_TCL_SET_MSK    0x00003e00
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING1_TCL register field value. */
#define ALT_SDR_CTL_DRAMTIMING1_TCL_CLR_MSK    0xffffc1ff
/* The reset value of the ALT_SDR_CTL_DRAMTIMING1_TCL register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING1_TCL_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING1_TCL field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING1_TCL_GET(value) (((value) & 0x00003e00) >> 9)
/* Produces a ALT_SDR_CTL_DRAMTIMING1_TCL register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING1_TCL_SET(value) (((value) << 9) & 0x00003e00)

/*
 * Field : Activate to Activate Delay - trrd
 * 
 * The activate to activate, different banks timing parameter.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING1_TRRD register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TRRD_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING1_TRRD register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TRRD_MSB        17
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING1_TRRD register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TRRD_WIDTH      4
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING1_TRRD register field value. */
#define ALT_SDR_CTL_DRAMTIMING1_TRRD_SET_MSK    0x0003c000
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING1_TRRD register field value. */
#define ALT_SDR_CTL_DRAMTIMING1_TRRD_CLR_MSK    0xfffc3fff
/* The reset value of the ALT_SDR_CTL_DRAMTIMING1_TRRD register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING1_TRRD_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING1_TRRD field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING1_TRRD_GET(value) (((value) & 0x0003c000) >> 14)
/* Produces a ALT_SDR_CTL_DRAMTIMING1_TRRD register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING1_TRRD_SET(value) (((value) << 14) & 0x0003c000)

/*
 * Field : Four Activate Window Time - tfaw
 * 
 * The four-activate window timing parameter.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING1_TFAW register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TFAW_LSB        18
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING1_TFAW register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TFAW_MSB        23
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING1_TFAW register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TFAW_WIDTH      6
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING1_TFAW register field value. */
#define ALT_SDR_CTL_DRAMTIMING1_TFAW_SET_MSK    0x00fc0000
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING1_TFAW register field value. */
#define ALT_SDR_CTL_DRAMTIMING1_TFAW_CLR_MSK    0xff03ffff
/* The reset value of the ALT_SDR_CTL_DRAMTIMING1_TFAW register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING1_TFAW_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING1_TFAW field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING1_TFAW_GET(value) (((value) & 0x00fc0000) >> 18)
/* Produces a ALT_SDR_CTL_DRAMTIMING1_TFAW register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING1_TFAW_SET(value) (((value) << 18) & 0x00fc0000)

/*
 * Field : Refresh Cycle Time - trfc
 * 
 * The refresh cycle timing parameter.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING1_TRFC register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TRFC_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING1_TRFC register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TRFC_MSB        31
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING1_TRFC register field. */
#define ALT_SDR_CTL_DRAMTIMING1_TRFC_WIDTH      8
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING1_TRFC register field value. */
#define ALT_SDR_CTL_DRAMTIMING1_TRFC_SET_MSK    0xff000000
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING1_TRFC register field value. */
#define ALT_SDR_CTL_DRAMTIMING1_TRFC_CLR_MSK    0x00ffffff
/* The reset value of the ALT_SDR_CTL_DRAMTIMING1_TRFC register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING1_TRFC_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING1_TRFC field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING1_TRFC_GET(value) (((value) & 0xff000000) >> 24)
/* Produces a ALT_SDR_CTL_DRAMTIMING1_TRFC register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING1_TRFC_SET(value) (((value) << 24) & 0xff000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_DRAMTIMING1.
 */
struct ALT_SDR_CTL_DRAMTIMING1_s
{
    uint32_t  tcwl :  4;  /* CAS Write Latency */
    uint32_t  tal  :  5;  /* Additive Latency */
    uint32_t  tcl  :  5;  /* CAS Read Latency */
    uint32_t  trrd :  4;  /* Activate to Activate Delay */
    uint32_t  tfaw :  6;  /* Four Activate Window Time */
    uint32_t  trfc :  8;  /* Refresh Cycle Time */
};

/* The typedef declaration for register ALT_SDR_CTL_DRAMTIMING1. */
typedef volatile struct ALT_SDR_CTL_DRAMTIMING1_s  ALT_SDR_CTL_DRAMTIMING1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_DRAMTIMING1 register from the beginning of the component. */
#define ALT_SDR_CTL_DRAMTIMING1_OFST        0x4

/*
 * Register : DRAM Timings 2 Register - dramtiming2
 * 
 * This register implements JEDEC standardized timing parameters.  It should be
 * programmed in clock cycles, for the value specified by the memory vendor.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                    
 * :--------|:-------|:--------|:--------------------------------
 *  [12:0]  | RW     | Unknown | Refresh Interval               
 *  [16:13] | RW     | Unknown | Activate to Read or Write Delay
 *  [20:17] | RW     | Unknown | Row Precharge Time             
 *  [24:21] | RW     | Unknown | Write Recovery Time            
 *  [28:25] | RW     | Unknown | Write to Read Time             
 *  [31:29] | ???    | 0x0     | *UNDEFINED*                    
 * 
 */
/*
 * Field : Refresh Interval - trefi
 * 
 * The refresh interval timing parameter.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING2_TREFI register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TREFI_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING2_TREFI register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TREFI_MSB        12
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING2_TREFI register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TREFI_WIDTH      13
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING2_TREFI register field value. */
#define ALT_SDR_CTL_DRAMTIMING2_TREFI_SET_MSK    0x00001fff
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING2_TREFI register field value. */
#define ALT_SDR_CTL_DRAMTIMING2_TREFI_CLR_MSK    0xffffe000
/* The reset value of the ALT_SDR_CTL_DRAMTIMING2_TREFI register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING2_TREFI_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING2_TREFI field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING2_TREFI_GET(value) (((value) & 0x00001fff) >> 0)
/* Produces a ALT_SDR_CTL_DRAMTIMING2_TREFI register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING2_TREFI_SET(value) (((value) << 0) & 0x00001fff)

/*
 * Field : Activate to Read or Write Delay - trcd
 * 
 * The activate to read/write timing parameter.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING2_TRCD register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TRCD_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING2_TRCD register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TRCD_MSB        16
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING2_TRCD register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TRCD_WIDTH      4
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING2_TRCD register field value. */
#define ALT_SDR_CTL_DRAMTIMING2_TRCD_SET_MSK    0x0001e000
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING2_TRCD register field value. */
#define ALT_SDR_CTL_DRAMTIMING2_TRCD_CLR_MSK    0xfffe1fff
/* The reset value of the ALT_SDR_CTL_DRAMTIMING2_TRCD register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING2_TRCD_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING2_TRCD field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING2_TRCD_GET(value) (((value) & 0x0001e000) >> 13)
/* Produces a ALT_SDR_CTL_DRAMTIMING2_TRCD register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING2_TRCD_SET(value) (((value) << 13) & 0x0001e000)

/*
 * Field : Row Precharge Time - trp
 * 
 * The precharge to activate timing parameter.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING2_TRP register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TRP_LSB        17
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING2_TRP register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TRP_MSB        20
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING2_TRP register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TRP_WIDTH      4
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING2_TRP register field value. */
#define ALT_SDR_CTL_DRAMTIMING2_TRP_SET_MSK    0x001e0000
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING2_TRP register field value. */
#define ALT_SDR_CTL_DRAMTIMING2_TRP_CLR_MSK    0xffe1ffff
/* The reset value of the ALT_SDR_CTL_DRAMTIMING2_TRP register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING2_TRP_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING2_TRP field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING2_TRP_GET(value) (((value) & 0x001e0000) >> 17)
/* Produces a ALT_SDR_CTL_DRAMTIMING2_TRP register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING2_TRP_SET(value) (((value) << 17) & 0x001e0000)

/*
 * Field : Write Recovery Time - twr
 * 
 * The write recovery timing.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING2_TWR register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TWR_LSB        21
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING2_TWR register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TWR_MSB        24
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING2_TWR register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TWR_WIDTH      4
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING2_TWR register field value. */
#define ALT_SDR_CTL_DRAMTIMING2_TWR_SET_MSK    0x01e00000
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING2_TWR register field value. */
#define ALT_SDR_CTL_DRAMTIMING2_TWR_CLR_MSK    0xfe1fffff
/* The reset value of the ALT_SDR_CTL_DRAMTIMING2_TWR register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING2_TWR_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING2_TWR field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING2_TWR_GET(value) (((value) & 0x01e00000) >> 21)
/* Produces a ALT_SDR_CTL_DRAMTIMING2_TWR register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING2_TWR_SET(value) (((value) << 21) & 0x01e00000)

/*
 * Field : Write to Read Time - twtr
 * 
 * The write to read timing parameter.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING2_TWTR register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TWTR_LSB        25
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING2_TWTR register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TWTR_MSB        28
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING2_TWTR register field. */
#define ALT_SDR_CTL_DRAMTIMING2_TWTR_WIDTH      4
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING2_TWTR register field value. */
#define ALT_SDR_CTL_DRAMTIMING2_TWTR_SET_MSK    0x1e000000
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING2_TWTR register field value. */
#define ALT_SDR_CTL_DRAMTIMING2_TWTR_CLR_MSK    0xe1ffffff
/* The reset value of the ALT_SDR_CTL_DRAMTIMING2_TWTR register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING2_TWTR_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING2_TWTR field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING2_TWTR_GET(value) (((value) & 0x1e000000) >> 25)
/* Produces a ALT_SDR_CTL_DRAMTIMING2_TWTR register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING2_TWTR_SET(value) (((value) << 25) & 0x1e000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_DRAMTIMING2.
 */
struct ALT_SDR_CTL_DRAMTIMING2_s
{
    uint32_t  trefi : 13;  /* Refresh Interval */
    uint32_t  trcd  :  4;  /* Activate to Read or Write Delay */
    uint32_t  trp   :  4;  /* Row Precharge Time */
    uint32_t  twr   :  4;  /* Write Recovery Time */
    uint32_t  twtr  :  4;  /* Write to Read Time */
    uint32_t        :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_DRAMTIMING2. */
typedef volatile struct ALT_SDR_CTL_DRAMTIMING2_s  ALT_SDR_CTL_DRAMTIMING2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_DRAMTIMING2 register from the beginning of the component. */
#define ALT_SDR_CTL_DRAMTIMING2_OFST        0x8

/*
 * Register : DRAM Timings 3 Register - dramtiming3
 * 
 * This register implements JEDEC standardized timing parameters.  It should be
 * programmed in clock cycles, for the value specified by the memory vendor.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                    
 * :--------|:-------|:--------|:--------------------------------
 *  [3:0]   | RW     | Unknown | Read to Precharge Time         
 *  [8:4]   | RW     | Unknown | Activate to Precharge Time     
 *  [14:9]  | RW     | Unknown | Row Cycle Time                 
 *  [18:15] | RW     | Unknown | Mode Register Programming Delay
 *  [22:19] | RW     | Unknown | CAS to CAS Delay               
 *  [31:23] | ???    | 0x0     | *UNDEFINED*                    
 * 
 */
/*
 * Field : Read to Precharge Time - trtp
 * 
 * The read to precharge timing parameter.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING3_TRTP register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TRTP_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING3_TRTP register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TRTP_MSB        3
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING3_TRTP register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TRTP_WIDTH      4
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING3_TRTP register field value. */
#define ALT_SDR_CTL_DRAMTIMING3_TRTP_SET_MSK    0x0000000f
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING3_TRTP register field value. */
#define ALT_SDR_CTL_DRAMTIMING3_TRTP_CLR_MSK    0xfffffff0
/* The reset value of the ALT_SDR_CTL_DRAMTIMING3_TRTP register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING3_TRTP_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING3_TRTP field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING3_TRTP_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_SDR_CTL_DRAMTIMING3_TRTP register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING3_TRTP_SET(value) (((value) << 0) & 0x0000000f)

/*
 * Field : Activate to Precharge Time - tras
 * 
 * The activate to precharge timing parameter.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING3_TRAS register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TRAS_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING3_TRAS register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TRAS_MSB        8
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING3_TRAS register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TRAS_WIDTH      5
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING3_TRAS register field value. */
#define ALT_SDR_CTL_DRAMTIMING3_TRAS_SET_MSK    0x000001f0
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING3_TRAS register field value. */
#define ALT_SDR_CTL_DRAMTIMING3_TRAS_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_SDR_CTL_DRAMTIMING3_TRAS register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING3_TRAS_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING3_TRAS field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING3_TRAS_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_SDR_CTL_DRAMTIMING3_TRAS register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING3_TRAS_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : Row Cycle Time - trc
 * 
 * The activate to activate timing parameter.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING3_TRC register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TRC_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING3_TRC register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TRC_MSB        14
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING3_TRC register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TRC_WIDTH      6
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING3_TRC register field value. */
#define ALT_SDR_CTL_DRAMTIMING3_TRC_SET_MSK    0x00007e00
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING3_TRC register field value. */
#define ALT_SDR_CTL_DRAMTIMING3_TRC_CLR_MSK    0xffff81ff
/* The reset value of the ALT_SDR_CTL_DRAMTIMING3_TRC register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING3_TRC_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING3_TRC field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING3_TRC_GET(value) (((value) & 0x00007e00) >> 9)
/* Produces a ALT_SDR_CTL_DRAMTIMING3_TRC register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING3_TRC_SET(value) (((value) << 9) & 0x00007e00)

/*
 * Field : Mode Register Programming Delay - tmrd
 * 
 * Mode register timing parameter.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING3_TMRD register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TMRD_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING3_TMRD register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TMRD_MSB        18
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING3_TMRD register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TMRD_WIDTH      4
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING3_TMRD register field value. */
#define ALT_SDR_CTL_DRAMTIMING3_TMRD_SET_MSK    0x00078000
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING3_TMRD register field value. */
#define ALT_SDR_CTL_DRAMTIMING3_TMRD_CLR_MSK    0xfff87fff
/* The reset value of the ALT_SDR_CTL_DRAMTIMING3_TMRD register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING3_TMRD_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING3_TMRD field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING3_TMRD_GET(value) (((value) & 0x00078000) >> 15)
/* Produces a ALT_SDR_CTL_DRAMTIMING3_TMRD register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING3_TMRD_SET(value) (((value) << 15) & 0x00078000)

/*
 * Field : CAS to CAS Delay - tccd
 * 
 * The CAS to CAS delay time.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING3_TCCD register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TCCD_LSB        19
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING3_TCCD register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TCCD_MSB        22
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING3_TCCD register field. */
#define ALT_SDR_CTL_DRAMTIMING3_TCCD_WIDTH      4
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING3_TCCD register field value. */
#define ALT_SDR_CTL_DRAMTIMING3_TCCD_SET_MSK    0x00780000
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING3_TCCD register field value. */
#define ALT_SDR_CTL_DRAMTIMING3_TCCD_CLR_MSK    0xff87ffff
/* The reset value of the ALT_SDR_CTL_DRAMTIMING3_TCCD register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING3_TCCD_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING3_TCCD field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING3_TCCD_GET(value) (((value) & 0x00780000) >> 19)
/* Produces a ALT_SDR_CTL_DRAMTIMING3_TCCD register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING3_TCCD_SET(value) (((value) << 19) & 0x00780000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_DRAMTIMING3.
 */
struct ALT_SDR_CTL_DRAMTIMING3_s
{
    uint32_t  trtp :  4;  /* Read to Precharge Time */
    uint32_t  tras :  5;  /* Activate to Precharge Time */
    uint32_t  trc  :  6;  /* Row Cycle Time */
    uint32_t  tmrd :  4;  /* Mode Register Programming Delay */
    uint32_t  tccd :  4;  /* CAS to CAS Delay */
    uint32_t       :  9;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_DRAMTIMING3. */
typedef volatile struct ALT_SDR_CTL_DRAMTIMING3_s  ALT_SDR_CTL_DRAMTIMING3_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_DRAMTIMING3 register from the beginning of the component. */
#define ALT_SDR_CTL_DRAMTIMING3_OFST        0xc

/*
 * Register : DRAM Timings 4 Register - dramtiming4
 * 
 * This register implements JEDEC standardized timing parameters.  It should be
 * programmed in clock cycles, for the value specified by the memory vendor.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                   
 * :--------|:-------|:--------|:-------------------------------
 *  [9:0]   | RW     | Unknown | Self-refresh Exit             
 *  [19:10] | RW     | Unknown | Power Down Exit               
 *  [23:20] | RW     | Unknown | Minimum Low Power State Cycles
 *  [31:24] | ???    | 0x0     | *UNDEFINED*                   
 * 
 */
/*
 * Field : Self-refresh Exit - selfrfshexit
 * 
 * The self refresh exit cycles, tXS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT register field. */
#define ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT register field. */
#define ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT_MSB        9
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT register field. */
#define ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT_WIDTH      10
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT register field value. */
#define ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT_SET_MSK    0x000003ff
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT register field value. */
#define ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT_CLR_MSK    0xfffffc00
/* The reset value of the ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT_GET(value) (((value) & 0x000003ff) >> 0)
/* Produces a ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING4_SELFRFSHEXIT_SET(value) (((value) << 0) & 0x000003ff)

/*
 * Field : Power Down Exit - pwrdownexit
 * 
 * The power down exit cycles, tXPDLL.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT register field. */
#define ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT register field. */
#define ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT_MSB        19
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT register field. */
#define ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT_WIDTH      10
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT register field value. */
#define ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT_SET_MSK    0x000ffc00
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT register field value. */
#define ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT_CLR_MSK    0xfff003ff
/* The reset value of the ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT_GET(value) (((value) & 0x000ffc00) >> 10)
/* Produces a ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING4_PWRDOWNEXIT_SET(value) (((value) << 10) & 0x000ffc00)

/*
 * Field : Minimum Low Power State Cycles - minpwrsavecycles
 * 
 * The minimum number of cycles to stay in a low power state. This applies to both
 * power down and self-refresh and should be set to the greater of tPD and tCKESR.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES register field. */
#define ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES_LSB        20
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES register field. */
#define ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES_MSB        23
/* The width in bits of the ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES register field. */
#define ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES_WIDTH      4
/* The mask used to set the ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES register field value. */
#define ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES_SET_MSK    0x00f00000
/* The mask used to clear the ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES register field value. */
#define ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES_CLR_MSK    0xff0fffff
/* The reset value of the ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES field value from a register. */
#define ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES_GET(value) (((value) & 0x00f00000) >> 20)
/* Produces a ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMTIMING4_MINPWRSAVECYCLES_SET(value) (((value) << 20) & 0x00f00000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_DRAMTIMING4.
 */
struct ALT_SDR_CTL_DRAMTIMING4_s
{
    uint32_t  selfrfshexit     : 10;  /* Self-refresh Exit */
    uint32_t  pwrdownexit      : 10;  /* Power Down Exit */
    uint32_t  minpwrsavecycles :  4;  /* Minimum Low Power State Cycles */
    uint32_t                   :  8;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_DRAMTIMING4. */
typedef volatile struct ALT_SDR_CTL_DRAMTIMING4_s  ALT_SDR_CTL_DRAMTIMING4_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_DRAMTIMING4 register from the beginning of the component. */
#define ALT_SDR_CTL_DRAMTIMING4_OFST        0x10

/*
 * Register : Lower Power Timing Register - lowpwrtiming
 * 
 * This register controls the behavior of the low power logic in the controller.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description               
 * :--------|:-------|:--------|:---------------------------
 *  [15:0]  | RW     | Unknown | Auto-power Down Cycles    
 *  [19:16] | RW     | Unknown | Clock Disable Delay Cycles
 *  [31:20] | ???    | 0x0     | *UNDEFINED*               
 * 
 */
/*
 * Field : Auto-power Down Cycles - autopdcycles
 * 
 * The number of idle clock cycles after which the controller should place the
 * memory into power-down mode.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES register field. */
#define ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES register field. */
#define ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES_MSB        15
/* The width in bits of the ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES register field. */
#define ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES_WIDTH      16
/* The mask used to set the ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES register field value. */
#define ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES_SET_MSK    0x0000ffff
/* The mask used to clear the ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES register field value. */
#define ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES_CLR_MSK    0xffff0000
/* The reset value of the ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES register field is UNKNOWN. */
#define ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES_RESET      0x0
/* Extracts the ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES field value from a register. */
#define ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES_GET(value) (((value) & 0x0000ffff) >> 0)
/* Produces a ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES register field value suitable for setting the register. */
#define ALT_SDR_CTL_LOWPWRTIMING_AUTOPDCYCLES_SET(value) (((value) << 0) & 0x0000ffff)

/*
 * Field : Clock Disable Delay Cycles - clkdisablecycles
 * 
 * Set to a the number of clocks after the execution of an self-refresh to stop the
 * clock.  This register is generally set based on PHY design latency and should
 * generally not be changed.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES register field. */
#define ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES register field. */
#define ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES_MSB        19
/* The width in bits of the ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES register field. */
#define ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES_WIDTH      4
/* The mask used to set the ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES register field value. */
#define ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES_SET_MSK    0x000f0000
/* The mask used to clear the ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES register field value. */
#define ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES_CLR_MSK    0xfff0ffff
/* The reset value of the ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES register field is UNKNOWN. */
#define ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES_RESET      0x0
/* Extracts the ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES field value from a register. */
#define ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES_GET(value) (((value) & 0x000f0000) >> 16)
/* Produces a ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES register field value suitable for setting the register. */
#define ALT_SDR_CTL_LOWPWRTIMING_CLKDISCYCLES_SET(value) (((value) << 16) & 0x000f0000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_LOWPWRTIMING.
 */
struct ALT_SDR_CTL_LOWPWRTIMING_s
{
    uint32_t  autopdcycles     : 16;  /* Auto-power Down Cycles */
    uint32_t  clkdisablecycles :  4;  /* Clock Disable Delay Cycles */
    uint32_t                   : 12;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_LOWPWRTIMING. */
typedef volatile struct ALT_SDR_CTL_LOWPWRTIMING_s  ALT_SDR_CTL_LOWPWRTIMING_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_LOWPWRTIMING register from the beginning of the component. */
#define ALT_SDR_CTL_LOWPWRTIMING_OFST        0x14

/*
 * Register : ODT Control Register - dramodt
 * 
 * This register controls which ODT pin is asserted during reads or writes. Bits
 * [1:0] control which ODT pin is asserted during to accesses to chip select 0,
 * bits [3:2] which ODT pin is asserted during accesses to chip select 1. For
 * example, a value of &quot;1001&quot; will cause ODT[0] to be asserted for
 * accesses to CS[0], and ODT[1] to be asserted for access to CS[1] pin. Set this
 * to &quot;0001&quot; if there is only one chip select available.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description      
 * :-------|:-------|:--------|:------------------
 *  [3:0]  | RW     | Unknown | Write ODT Control
 *  [7:4]  | RW     | Unknown | Read ODT Control 
 *  [31:8] | ???    | 0x0     | *UNDEFINED*      
 * 
 */
/*
 * Field : Write ODT Control - cfg_write_odt_chip
 * 
 * This register controls which ODT pin is asserted during writes.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP register field. */
#define ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP register field. */
#define ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP_MSB        3
/* The width in bits of the ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP register field. */
#define ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP_WIDTH      4
/* The mask used to set the ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP register field value. */
#define ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP_SET_MSK    0x0000000f
/* The mask used to clear the ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP register field value. */
#define ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP_CLR_MSK    0xfffffff0
/* The reset value of the ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP field value from a register. */
#define ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMODT_CFG_WR_ODT_CHIP_SET(value) (((value) << 0) & 0x0000000f)

/*
 * Field : Read ODT Control - cfg_read_odt_chip
 * 
 * This register controls which ODT pin is asserted during reads.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP register field. */
#define ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP register field. */
#define ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP_MSB        7
/* The width in bits of the ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP register field. */
#define ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP_WIDTH      4
/* The mask used to set the ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP register field value. */
#define ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP_SET_MSK    0x000000f0
/* The mask used to clear the ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP register field value. */
#define ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP_CLR_MSK    0xffffff0f
/* The reset value of the ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP field value from a register. */
#define ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP_GET(value) (((value) & 0x000000f0) >> 4)
/* Produces a ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMODT_CFG_RD_ODT_CHIP_SET(value) (((value) << 4) & 0x000000f0)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_DRAMODT.
 */
struct ALT_SDR_CTL_DRAMODT_s
{
    uint32_t  cfg_write_odt_chip :  4;  /* Write ODT Control */
    uint32_t  cfg_read_odt_chip  :  4;  /* Read ODT Control */
    uint32_t                     : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_DRAMODT. */
typedef volatile struct ALT_SDR_CTL_DRAMODT_s  ALT_SDR_CTL_DRAMODT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_DRAMODT register from the beginning of the component. */
#define ALT_SDR_CTL_DRAMODT_OFST        0x18

/*
 * Register : DRAM Address Widths Register - dramaddrw
 * 
 * This register configures the width of the various address fields of the DRAM.
 * The values specified in this register must match the memory devices being used.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description             
 * :--------|:-------|:--------|:-------------------------
 *  [4:0]   | RW     | Unknown | DRAM Column Address Bits
 *  [9:5]   | RW     | Unknown | DRAM Row Address Bits   
 *  [12:10] | RW     | Unknown | DRAM Bank Address Bits  
 *  [15:13] | RW     | Unknown | DRAM Chip Address Bits  
 *  [31:16] | ???    | 0x0     | *UNDEFINED*             
 * 
 */
/*
 * Field : DRAM Column Address Bits - colbits
 * 
 * The number of column address bits for the memory devices in your memory
 * interface.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMADDRW_COLBITS register field. */
#define ALT_SDR_CTL_DRAMADDRW_COLBITS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMADDRW_COLBITS register field. */
#define ALT_SDR_CTL_DRAMADDRW_COLBITS_MSB        4
/* The width in bits of the ALT_SDR_CTL_DRAMADDRW_COLBITS register field. */
#define ALT_SDR_CTL_DRAMADDRW_COLBITS_WIDTH      5
/* The mask used to set the ALT_SDR_CTL_DRAMADDRW_COLBITS register field value. */
#define ALT_SDR_CTL_DRAMADDRW_COLBITS_SET_MSK    0x0000001f
/* The mask used to clear the ALT_SDR_CTL_DRAMADDRW_COLBITS register field value. */
#define ALT_SDR_CTL_DRAMADDRW_COLBITS_CLR_MSK    0xffffffe0
/* The reset value of the ALT_SDR_CTL_DRAMADDRW_COLBITS register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMADDRW_COLBITS_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMADDRW_COLBITS field value from a register. */
#define ALT_SDR_CTL_DRAMADDRW_COLBITS_GET(value) (((value) & 0x0000001f) >> 0)
/* Produces a ALT_SDR_CTL_DRAMADDRW_COLBITS register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMADDRW_COLBITS_SET(value) (((value) << 0) & 0x0000001f)

/*
 * Field : DRAM Row Address Bits - rowbits
 * 
 * The number of row address bits for the memory devices in your memory interface.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMADDRW_ROWBITS register field. */
#define ALT_SDR_CTL_DRAMADDRW_ROWBITS_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMADDRW_ROWBITS register field. */
#define ALT_SDR_CTL_DRAMADDRW_ROWBITS_MSB        9
/* The width in bits of the ALT_SDR_CTL_DRAMADDRW_ROWBITS register field. */
#define ALT_SDR_CTL_DRAMADDRW_ROWBITS_WIDTH      5
/* The mask used to set the ALT_SDR_CTL_DRAMADDRW_ROWBITS register field value. */
#define ALT_SDR_CTL_DRAMADDRW_ROWBITS_SET_MSK    0x000003e0
/* The mask used to clear the ALT_SDR_CTL_DRAMADDRW_ROWBITS register field value. */
#define ALT_SDR_CTL_DRAMADDRW_ROWBITS_CLR_MSK    0xfffffc1f
/* The reset value of the ALT_SDR_CTL_DRAMADDRW_ROWBITS register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMADDRW_ROWBITS_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMADDRW_ROWBITS field value from a register. */
#define ALT_SDR_CTL_DRAMADDRW_ROWBITS_GET(value) (((value) & 0x000003e0) >> 5)
/* Produces a ALT_SDR_CTL_DRAMADDRW_ROWBITS register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMADDRW_ROWBITS_SET(value) (((value) << 5) & 0x000003e0)

/*
 * Field : DRAM Bank Address Bits - bankbits
 * 
 * The number of bank address bits for the memory devices in your memory interface.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMADDRW_BANKBITS register field. */
#define ALT_SDR_CTL_DRAMADDRW_BANKBITS_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMADDRW_BANKBITS register field. */
#define ALT_SDR_CTL_DRAMADDRW_BANKBITS_MSB        12
/* The width in bits of the ALT_SDR_CTL_DRAMADDRW_BANKBITS register field. */
#define ALT_SDR_CTL_DRAMADDRW_BANKBITS_WIDTH      3
/* The mask used to set the ALT_SDR_CTL_DRAMADDRW_BANKBITS register field value. */
#define ALT_SDR_CTL_DRAMADDRW_BANKBITS_SET_MSK    0x00001c00
/* The mask used to clear the ALT_SDR_CTL_DRAMADDRW_BANKBITS register field value. */
#define ALT_SDR_CTL_DRAMADDRW_BANKBITS_CLR_MSK    0xffffe3ff
/* The reset value of the ALT_SDR_CTL_DRAMADDRW_BANKBITS register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMADDRW_BANKBITS_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMADDRW_BANKBITS field value from a register. */
#define ALT_SDR_CTL_DRAMADDRW_BANKBITS_GET(value) (((value) & 0x00001c00) >> 10)
/* Produces a ALT_SDR_CTL_DRAMADDRW_BANKBITS register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMADDRW_BANKBITS_SET(value) (((value) << 10) & 0x00001c00)

/*
 * Field : DRAM Chip Address Bits - csbits
 * 
 * The number of chip select address bits for the memory devices in your memory
 * interface.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMADDRW_CSBITS register field. */
#define ALT_SDR_CTL_DRAMADDRW_CSBITS_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMADDRW_CSBITS register field. */
#define ALT_SDR_CTL_DRAMADDRW_CSBITS_MSB        15
/* The width in bits of the ALT_SDR_CTL_DRAMADDRW_CSBITS register field. */
#define ALT_SDR_CTL_DRAMADDRW_CSBITS_WIDTH      3
/* The mask used to set the ALT_SDR_CTL_DRAMADDRW_CSBITS register field value. */
#define ALT_SDR_CTL_DRAMADDRW_CSBITS_SET_MSK    0x0000e000
/* The mask used to clear the ALT_SDR_CTL_DRAMADDRW_CSBITS register field value. */
#define ALT_SDR_CTL_DRAMADDRW_CSBITS_CLR_MSK    0xffff1fff
/* The reset value of the ALT_SDR_CTL_DRAMADDRW_CSBITS register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMADDRW_CSBITS_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMADDRW_CSBITS field value from a register. */
#define ALT_SDR_CTL_DRAMADDRW_CSBITS_GET(value) (((value) & 0x0000e000) >> 13)
/* Produces a ALT_SDR_CTL_DRAMADDRW_CSBITS register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMADDRW_CSBITS_SET(value) (((value) << 13) & 0x0000e000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_DRAMADDRW.
 */
struct ALT_SDR_CTL_DRAMADDRW_s
{
    uint32_t  colbits  :  5;  /* DRAM Column Address Bits */
    uint32_t  rowbits  :  5;  /* DRAM Row Address Bits */
    uint32_t  bankbits :  3;  /* DRAM Bank Address Bits */
    uint32_t  csbits   :  3;  /* DRAM Chip Address Bits */
    uint32_t           : 16;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_DRAMADDRW. */
typedef volatile struct ALT_SDR_CTL_DRAMADDRW_s  ALT_SDR_CTL_DRAMADDRW_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_DRAMADDRW register from the beginning of the component. */
#define ALT_SDR_CTL_DRAMADDRW_OFST        0x2c

/*
 * Register : DRAM Interface Data Width Register - dramifwidth
 * 
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description              
 * :-------|:-------|:--------|:--------------------------
 *  [7:0]  | RW     | Unknown | DRAM Interface Data Width
 *  [31:8] | ???    | 0x0     | *UNDEFINED*              
 * 
 */
/*
 * Field : DRAM Interface Data Width - ifwidth
 * 
 * This register controls the interface width of the SDRAM interface, including any
 * bits used for ECC. For example, for a 32-bit interface with ECC, program this
 * register with 0x28. You must also program the ctrlwidth register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH register field. */
#define ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH register field. */
#define ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH_MSB        7
/* The width in bits of the ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH register field. */
#define ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH_WIDTH      8
/* The mask used to set the ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH register field value. */
#define ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH register field value. */
#define ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH_CLR_MSK    0xffffff00
/* The reset value of the ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH field value from a register. */
#define ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMIFWIDTH_IFWIDTH_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_DRAMIFWIDTH.
 */
struct ALT_SDR_CTL_DRAMIFWIDTH_s
{
    uint32_t  ifwidth :  8;  /* DRAM Interface Data Width */
    uint32_t          : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_DRAMIFWIDTH. */
typedef volatile struct ALT_SDR_CTL_DRAMIFWIDTH_s  ALT_SDR_CTL_DRAMIFWIDTH_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_DRAMIFWIDTH register from the beginning of the component. */
#define ALT_SDR_CTL_DRAMIFWIDTH_OFST        0x30

/*
 * Register : DRAM Devices Data Width Register - dramdevwidth
 * 
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description            
 * :-------|:-------|:--------|:------------------------
 *  [3:0]  | RW     | Unknown | DRAM Devices Data Width
 *  [31:4] | ???    | 0x0     | *UNDEFINED*            
 * 
 */
/*
 * Field : DRAM Devices Data Width - devwidth
 * 
 * This register specifies the width of the physical DRAM chips, for example 8 or
 * 16.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH register field. */
#define ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH register field. */
#define ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH_MSB        3
/* The width in bits of the ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH register field. */
#define ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH_WIDTH      4
/* The mask used to set the ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH register field value. */
#define ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH_SET_MSK    0x0000000f
/* The mask used to clear the ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH register field value. */
#define ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH_CLR_MSK    0xfffffff0
/* The reset value of the ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH field value from a register. */
#define ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMDEVWIDTH_DEVWIDTH_SET(value) (((value) << 0) & 0x0000000f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_DRAMDEVWIDTH.
 */
struct ALT_SDR_CTL_DRAMDEVWIDTH_s
{
    uint32_t  devwidth :  4;  /* DRAM Devices Data Width */
    uint32_t           : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_DRAMDEVWIDTH. */
typedef volatile struct ALT_SDR_CTL_DRAMDEVWIDTH_s  ALT_SDR_CTL_DRAMDEVWIDTH_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_DRAMDEVWIDTH register from the beginning of the component. */
#define ALT_SDR_CTL_DRAMDEVWIDTH_OFST        0x34

/*
 * Register : DRAM Status Register - dramsts
 * 
 * This register provides the status of the calibration and ECC logic.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description                
 * :-------|:-------|:--------|:----------------------------
 *  [0]    | RW     | Unknown | PHY Calibration Successful 
 *  [1]    | RW     | Unknown | PHY Calibration Failed     
 *  [2]    | RW     | Unknown | Single Bit Error Seen      
 *  [3]    | RW     | Unknown | Double Bit Error Seen      
 *  [4]    | RW     | Unknown | ECC Auto-Correction Dropped
 *  [31:5] | ???    | 0x0     | *UNDEFINED*                
 * 
 */
/*
 * Field : PHY Calibration Successful - calsuccess
 * 
 * This bit will be set to 1 if the PHY was able to successfully calibrate.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMSTS_CALSUCCESS register field. */
#define ALT_SDR_CTL_DRAMSTS_CALSUCCESS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMSTS_CALSUCCESS register field. */
#define ALT_SDR_CTL_DRAMSTS_CALSUCCESS_MSB        0
/* The width in bits of the ALT_SDR_CTL_DRAMSTS_CALSUCCESS register field. */
#define ALT_SDR_CTL_DRAMSTS_CALSUCCESS_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_DRAMSTS_CALSUCCESS register field value. */
#define ALT_SDR_CTL_DRAMSTS_CALSUCCESS_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDR_CTL_DRAMSTS_CALSUCCESS register field value. */
#define ALT_SDR_CTL_DRAMSTS_CALSUCCESS_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDR_CTL_DRAMSTS_CALSUCCESS register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMSTS_CALSUCCESS_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMSTS_CALSUCCESS field value from a register. */
#define ALT_SDR_CTL_DRAMSTS_CALSUCCESS_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDR_CTL_DRAMSTS_CALSUCCESS register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMSTS_CALSUCCESS_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : PHY Calibration Failed - calfail
 * 
 * This bit  will be set to 1 if the PHY was unable to calibrate.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMSTS_CALFAIL register field. */
#define ALT_SDR_CTL_DRAMSTS_CALFAIL_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMSTS_CALFAIL register field. */
#define ALT_SDR_CTL_DRAMSTS_CALFAIL_MSB        1
/* The width in bits of the ALT_SDR_CTL_DRAMSTS_CALFAIL register field. */
#define ALT_SDR_CTL_DRAMSTS_CALFAIL_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_DRAMSTS_CALFAIL register field value. */
#define ALT_SDR_CTL_DRAMSTS_CALFAIL_SET_MSK    0x00000002
/* The mask used to clear the ALT_SDR_CTL_DRAMSTS_CALFAIL register field value. */
#define ALT_SDR_CTL_DRAMSTS_CALFAIL_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SDR_CTL_DRAMSTS_CALFAIL register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMSTS_CALFAIL_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMSTS_CALFAIL field value from a register. */
#define ALT_SDR_CTL_DRAMSTS_CALFAIL_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SDR_CTL_DRAMSTS_CALFAIL register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMSTS_CALFAIL_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Single Bit Error Seen - sbeerr
 * 
 * This bit will be set to 1 if there have been any ECC single bit errors detected.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMSTS_SBEERR register field. */
#define ALT_SDR_CTL_DRAMSTS_SBEERR_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMSTS_SBEERR register field. */
#define ALT_SDR_CTL_DRAMSTS_SBEERR_MSB        2
/* The width in bits of the ALT_SDR_CTL_DRAMSTS_SBEERR register field. */
#define ALT_SDR_CTL_DRAMSTS_SBEERR_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_DRAMSTS_SBEERR register field value. */
#define ALT_SDR_CTL_DRAMSTS_SBEERR_SET_MSK    0x00000004
/* The mask used to clear the ALT_SDR_CTL_DRAMSTS_SBEERR register field value. */
#define ALT_SDR_CTL_DRAMSTS_SBEERR_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SDR_CTL_DRAMSTS_SBEERR register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMSTS_SBEERR_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMSTS_SBEERR field value from a register. */
#define ALT_SDR_CTL_DRAMSTS_SBEERR_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SDR_CTL_DRAMSTS_SBEERR register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMSTS_SBEERR_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Double Bit Error Seen - dbeerr
 * 
 * This bit will be set to 1 if there have been any ECC double bit errors detected.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMSTS_DBEERR register field. */
#define ALT_SDR_CTL_DRAMSTS_DBEERR_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMSTS_DBEERR register field. */
#define ALT_SDR_CTL_DRAMSTS_DBEERR_MSB        3
/* The width in bits of the ALT_SDR_CTL_DRAMSTS_DBEERR register field. */
#define ALT_SDR_CTL_DRAMSTS_DBEERR_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_DRAMSTS_DBEERR register field value. */
#define ALT_SDR_CTL_DRAMSTS_DBEERR_SET_MSK    0x00000008
/* The mask used to clear the ALT_SDR_CTL_DRAMSTS_DBEERR register field value. */
#define ALT_SDR_CTL_DRAMSTS_DBEERR_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SDR_CTL_DRAMSTS_DBEERR register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMSTS_DBEERR_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMSTS_DBEERR field value from a register. */
#define ALT_SDR_CTL_DRAMSTS_DBEERR_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SDR_CTL_DRAMSTS_DBEERR register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMSTS_DBEERR_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : ECC Auto-Correction Dropped - corrdrop
 * 
 * This bit will be set to 1 if there any auto-corrections have been dropped.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMSTS_CORRDROP register field. */
#define ALT_SDR_CTL_DRAMSTS_CORRDROP_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMSTS_CORRDROP register field. */
#define ALT_SDR_CTL_DRAMSTS_CORRDROP_MSB        4
/* The width in bits of the ALT_SDR_CTL_DRAMSTS_CORRDROP register field. */
#define ALT_SDR_CTL_DRAMSTS_CORRDROP_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_DRAMSTS_CORRDROP register field value. */
#define ALT_SDR_CTL_DRAMSTS_CORRDROP_SET_MSK    0x00000010
/* The mask used to clear the ALT_SDR_CTL_DRAMSTS_CORRDROP register field value. */
#define ALT_SDR_CTL_DRAMSTS_CORRDROP_CLR_MSK    0xffffffef
/* The reset value of the ALT_SDR_CTL_DRAMSTS_CORRDROP register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMSTS_CORRDROP_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMSTS_CORRDROP field value from a register. */
#define ALT_SDR_CTL_DRAMSTS_CORRDROP_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SDR_CTL_DRAMSTS_CORRDROP register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMSTS_CORRDROP_SET(value) (((value) << 4) & 0x00000010)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_DRAMSTS.
 */
struct ALT_SDR_CTL_DRAMSTS_s
{
    uint32_t  calsuccess :  1;  /* PHY Calibration Successful */
    uint32_t  calfail    :  1;  /* PHY Calibration Failed */
    uint32_t  sbeerr     :  1;  /* Single Bit Error Seen */
    uint32_t  dbeerr     :  1;  /* Double Bit Error Seen */
    uint32_t  corrdrop   :  1;  /* ECC Auto-Correction Dropped */
    uint32_t             : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_DRAMSTS. */
typedef volatile struct ALT_SDR_CTL_DRAMSTS_s  ALT_SDR_CTL_DRAMSTS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_DRAMSTS register from the beginning of the component. */
#define ALT_SDR_CTL_DRAMSTS_OFST        0x38

/*
 * Register : ECC Interrupt  Register - dramintr
 * 
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description                           
 * :-------|:-------|:--------|:---------------------------------------
 *  [0]    | RW     | Unknown | Interrupt Enable                      
 *  [1]    | RW     | Unknown | Mask Single Bit Error Interrupt       
 *  [2]    | RW     | Unknown | Mask Double Bit Error Interrupt       
 *  [3]    | RW     | Unknown | Mask Dropped Auto-correction Interrupt
 *  [4]    | RW     | Unknown | Clear Interrupt Signal                
 *  [31:5] | ???    | 0x0     | *UNDEFINED*                           
 * 
 */
/*
 * Field : Interrupt Enable - intren
 * 
 * Enable the interrupt output.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMINTR_INTREN register field. */
#define ALT_SDR_CTL_DRAMINTR_INTREN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMINTR_INTREN register field. */
#define ALT_SDR_CTL_DRAMINTR_INTREN_MSB        0
/* The width in bits of the ALT_SDR_CTL_DRAMINTR_INTREN register field. */
#define ALT_SDR_CTL_DRAMINTR_INTREN_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_DRAMINTR_INTREN register field value. */
#define ALT_SDR_CTL_DRAMINTR_INTREN_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDR_CTL_DRAMINTR_INTREN register field value. */
#define ALT_SDR_CTL_DRAMINTR_INTREN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDR_CTL_DRAMINTR_INTREN register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMINTR_INTREN_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMINTR_INTREN field value from a register. */
#define ALT_SDR_CTL_DRAMINTR_INTREN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDR_CTL_DRAMINTR_INTREN register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMINTR_INTREN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Mask Single Bit Error Interrupt - sbemask
 * 
 * Mask the single bit error interrupt.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMINTR_SBEMSK register field. */
#define ALT_SDR_CTL_DRAMINTR_SBEMSK_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMINTR_SBEMSK register field. */
#define ALT_SDR_CTL_DRAMINTR_SBEMSK_MSB        1
/* The width in bits of the ALT_SDR_CTL_DRAMINTR_SBEMSK register field. */
#define ALT_SDR_CTL_DRAMINTR_SBEMSK_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_DRAMINTR_SBEMSK register field value. */
#define ALT_SDR_CTL_DRAMINTR_SBEMSK_SET_MSK    0x00000002
/* The mask used to clear the ALT_SDR_CTL_DRAMINTR_SBEMSK register field value. */
#define ALT_SDR_CTL_DRAMINTR_SBEMSK_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SDR_CTL_DRAMINTR_SBEMSK register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMINTR_SBEMSK_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMINTR_SBEMSK field value from a register. */
#define ALT_SDR_CTL_DRAMINTR_SBEMSK_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SDR_CTL_DRAMINTR_SBEMSK register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMINTR_SBEMSK_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Mask Double Bit Error Interrupt - dbemask
 * 
 * Mask the double bit error interrupt.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMINTR_DBEMSK register field. */
#define ALT_SDR_CTL_DRAMINTR_DBEMSK_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMINTR_DBEMSK register field. */
#define ALT_SDR_CTL_DRAMINTR_DBEMSK_MSB        2
/* The width in bits of the ALT_SDR_CTL_DRAMINTR_DBEMSK register field. */
#define ALT_SDR_CTL_DRAMINTR_DBEMSK_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_DRAMINTR_DBEMSK register field value. */
#define ALT_SDR_CTL_DRAMINTR_DBEMSK_SET_MSK    0x00000004
/* The mask used to clear the ALT_SDR_CTL_DRAMINTR_DBEMSK register field value. */
#define ALT_SDR_CTL_DRAMINTR_DBEMSK_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SDR_CTL_DRAMINTR_DBEMSK register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMINTR_DBEMSK_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMINTR_DBEMSK field value from a register. */
#define ALT_SDR_CTL_DRAMINTR_DBEMSK_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SDR_CTL_DRAMINTR_DBEMSK register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMINTR_DBEMSK_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Mask Dropped Auto-correction Interrupt - corrdropmask
 * 
 * Set this bit to a one to mask interrupts for an ECC correction write back
 * needing to be dropped.  This indicates a burst of memory errors in a short
 * period of time.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMINTR_CORRDROPMSK register field. */
#define ALT_SDR_CTL_DRAMINTR_CORRDROPMSK_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMINTR_CORRDROPMSK register field. */
#define ALT_SDR_CTL_DRAMINTR_CORRDROPMSK_MSB        3
/* The width in bits of the ALT_SDR_CTL_DRAMINTR_CORRDROPMSK register field. */
#define ALT_SDR_CTL_DRAMINTR_CORRDROPMSK_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_DRAMINTR_CORRDROPMSK register field value. */
#define ALT_SDR_CTL_DRAMINTR_CORRDROPMSK_SET_MSK    0x00000008
/* The mask used to clear the ALT_SDR_CTL_DRAMINTR_CORRDROPMSK register field value. */
#define ALT_SDR_CTL_DRAMINTR_CORRDROPMSK_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SDR_CTL_DRAMINTR_CORRDROPMSK register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMINTR_CORRDROPMSK_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMINTR_CORRDROPMSK field value from a register. */
#define ALT_SDR_CTL_DRAMINTR_CORRDROPMSK_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SDR_CTL_DRAMINTR_CORRDROPMSK register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMINTR_CORRDROPMSK_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Clear Interrupt Signal - intrclr
 * 
 * Writing to this self-clearing bit clears the interrupt signal. Writing to this
 * bit also clears the error count and error address registers.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DRAMINTR_INTRCLR register field. */
#define ALT_SDR_CTL_DRAMINTR_INTRCLR_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DRAMINTR_INTRCLR register field. */
#define ALT_SDR_CTL_DRAMINTR_INTRCLR_MSB        4
/* The width in bits of the ALT_SDR_CTL_DRAMINTR_INTRCLR register field. */
#define ALT_SDR_CTL_DRAMINTR_INTRCLR_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_DRAMINTR_INTRCLR register field value. */
#define ALT_SDR_CTL_DRAMINTR_INTRCLR_SET_MSK    0x00000010
/* The mask used to clear the ALT_SDR_CTL_DRAMINTR_INTRCLR register field value. */
#define ALT_SDR_CTL_DRAMINTR_INTRCLR_CLR_MSK    0xffffffef
/* The reset value of the ALT_SDR_CTL_DRAMINTR_INTRCLR register field is UNKNOWN. */
#define ALT_SDR_CTL_DRAMINTR_INTRCLR_RESET      0x0
/* Extracts the ALT_SDR_CTL_DRAMINTR_INTRCLR field value from a register. */
#define ALT_SDR_CTL_DRAMINTR_INTRCLR_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_SDR_CTL_DRAMINTR_INTRCLR register field value suitable for setting the register. */
#define ALT_SDR_CTL_DRAMINTR_INTRCLR_SET(value) (((value) << 4) & 0x00000010)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_DRAMINTR.
 */
struct ALT_SDR_CTL_DRAMINTR_s
{
    uint32_t  intren       :  1;  /* Interrupt Enable */
    uint32_t  sbemask      :  1;  /* Mask Single Bit Error Interrupt */
    uint32_t  dbemask      :  1;  /* Mask Double Bit Error Interrupt */
    uint32_t  corrdropmask :  1;  /* Mask Dropped Auto-correction Interrupt */
    uint32_t  intrclr      :  1;  /* Clear Interrupt Signal */
    uint32_t               : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_DRAMINTR. */
typedef volatile struct ALT_SDR_CTL_DRAMINTR_s  ALT_SDR_CTL_DRAMINTR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_DRAMINTR register from the beginning of the component. */
#define ALT_SDR_CTL_DRAMINTR_OFST        0x3c

/*
 * Register : ECC Single Bit Error Count Register - sbecount
 * 
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description           
 * :-------|:-------|:--------|:-----------------------
 *  [7:0]  | RW     | Unknown | Single Bit Error Count
 *  [31:8] | ???    | 0x0     | *UNDEFINED*           
 * 
 */
/*
 * Field : Single Bit Error Count - count
 * 
 * Reports the number of single bit errors that have occurred since the status
 * register counters were last cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_SBECOUNT_COUNT register field. */
#define ALT_SDR_CTL_SBECOUNT_COUNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_SBECOUNT_COUNT register field. */
#define ALT_SDR_CTL_SBECOUNT_COUNT_MSB        7
/* The width in bits of the ALT_SDR_CTL_SBECOUNT_COUNT register field. */
#define ALT_SDR_CTL_SBECOUNT_COUNT_WIDTH      8
/* The mask used to set the ALT_SDR_CTL_SBECOUNT_COUNT register field value. */
#define ALT_SDR_CTL_SBECOUNT_COUNT_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SDR_CTL_SBECOUNT_COUNT register field value. */
#define ALT_SDR_CTL_SBECOUNT_COUNT_CLR_MSK    0xffffff00
/* The reset value of the ALT_SDR_CTL_SBECOUNT_COUNT register field is UNKNOWN. */
#define ALT_SDR_CTL_SBECOUNT_COUNT_RESET      0x0
/* Extracts the ALT_SDR_CTL_SBECOUNT_COUNT field value from a register. */
#define ALT_SDR_CTL_SBECOUNT_COUNT_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SDR_CTL_SBECOUNT_COUNT register field value suitable for setting the register. */
#define ALT_SDR_CTL_SBECOUNT_COUNT_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_SBECOUNT.
 */
struct ALT_SDR_CTL_SBECOUNT_s
{
    uint32_t  count :  8;  /* Single Bit Error Count */
    uint32_t        : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_SBECOUNT. */
typedef volatile struct ALT_SDR_CTL_SBECOUNT_s  ALT_SDR_CTL_SBECOUNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_SBECOUNT register from the beginning of the component. */
#define ALT_SDR_CTL_SBECOUNT_OFST        0x40

/*
 * Register : ECC Double Bit Error Count Register - dbecount
 * 
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description           
 * :-------|:-------|:--------|:-----------------------
 *  [7:0]  | RW     | Unknown | Double Bit Error Count
 *  [31:8] | ???    | 0x0     | *UNDEFINED*           
 * 
 */
/*
 * Field : Double Bit Error Count - count
 * 
 * Reports the number of double bit errors that have occurred since the status
 * register counters were last cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DBECOUNT_COUNT register field. */
#define ALT_SDR_CTL_DBECOUNT_COUNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DBECOUNT_COUNT register field. */
#define ALT_SDR_CTL_DBECOUNT_COUNT_MSB        7
/* The width in bits of the ALT_SDR_CTL_DBECOUNT_COUNT register field. */
#define ALT_SDR_CTL_DBECOUNT_COUNT_WIDTH      8
/* The mask used to set the ALT_SDR_CTL_DBECOUNT_COUNT register field value. */
#define ALT_SDR_CTL_DBECOUNT_COUNT_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SDR_CTL_DBECOUNT_COUNT register field value. */
#define ALT_SDR_CTL_DBECOUNT_COUNT_CLR_MSK    0xffffff00
/* The reset value of the ALT_SDR_CTL_DBECOUNT_COUNT register field is UNKNOWN. */
#define ALT_SDR_CTL_DBECOUNT_COUNT_RESET      0x0
/* Extracts the ALT_SDR_CTL_DBECOUNT_COUNT field value from a register. */
#define ALT_SDR_CTL_DBECOUNT_COUNT_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SDR_CTL_DBECOUNT_COUNT register field value suitable for setting the register. */
#define ALT_SDR_CTL_DBECOUNT_COUNT_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_DBECOUNT.
 */
struct ALT_SDR_CTL_DBECOUNT_s
{
    uint32_t  count :  8;  /* Double Bit Error Count */
    uint32_t        : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_DBECOUNT. */
typedef volatile struct ALT_SDR_CTL_DBECOUNT_s  ALT_SDR_CTL_DBECOUNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_DBECOUNT register from the beginning of the component. */
#define ALT_SDR_CTL_DBECOUNT_OFST        0x44

/*
 * Register : ECC Error Address Register - erraddr
 * 
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description      
 * :-------|:-------|:--------|:------------------
 *  [31:0] | RW     | Unknown | ECC Error Address
 * 
 */
/*
 * Field : ECC Error Address - addr
 * 
 * The address of the most recent ECC error.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_ERRADDR_ADDR register field. */
#define ALT_SDR_CTL_ERRADDR_ADDR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_ERRADDR_ADDR register field. */
#define ALT_SDR_CTL_ERRADDR_ADDR_MSB        31
/* The width in bits of the ALT_SDR_CTL_ERRADDR_ADDR register field. */
#define ALT_SDR_CTL_ERRADDR_ADDR_WIDTH      32
/* The mask used to set the ALT_SDR_CTL_ERRADDR_ADDR register field value. */
#define ALT_SDR_CTL_ERRADDR_ADDR_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDR_CTL_ERRADDR_ADDR register field value. */
#define ALT_SDR_CTL_ERRADDR_ADDR_CLR_MSK    0x00000000
/* The reset value of the ALT_SDR_CTL_ERRADDR_ADDR register field is UNKNOWN. */
#define ALT_SDR_CTL_ERRADDR_ADDR_RESET      0x0
/* Extracts the ALT_SDR_CTL_ERRADDR_ADDR field value from a register. */
#define ALT_SDR_CTL_ERRADDR_ADDR_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDR_CTL_ERRADDR_ADDR register field value suitable for setting the register. */
#define ALT_SDR_CTL_ERRADDR_ADDR_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_ERRADDR.
 */
struct ALT_SDR_CTL_ERRADDR_s
{
    uint32_t  addr : 32;  /* ECC Error Address */
};

/* The typedef declaration for register ALT_SDR_CTL_ERRADDR. */
typedef volatile struct ALT_SDR_CTL_ERRADDR_s  ALT_SDR_CTL_ERRADDR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_ERRADDR register from the beginning of the component. */
#define ALT_SDR_CTL_ERRADDR_OFST        0x48

/*
 * Register : ECC Auto-correction Dropped Count Register - dropcount
 * 
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description                  
 * :-------|:-------|:--------|:------------------------------
 *  [7:0]  | RW     | Unknown | Dropped Auto-correction Count
 *  [31:8] | ???    | 0x0     | *UNDEFINED*                  
 * 
 */
/*
 * Field : Dropped Auto-correction Count - corrdropcount
 * 
 * This gives the count of the number of ECC write back transactions dropped due to
 * the internal FIFO overflowing.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT register field. */
#define ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT register field. */
#define ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT_MSB        7
/* The width in bits of the ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT register field. */
#define ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT_WIDTH      8
/* The mask used to set the ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT register field value. */
#define ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT register field value. */
#define ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT_CLR_MSK    0xffffff00
/* The reset value of the ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT register field is UNKNOWN. */
#define ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT_RESET      0x0
/* Extracts the ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT field value from a register. */
#define ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT register field value suitable for setting the register. */
#define ALT_SDR_CTL_DROPCOUNT_CORRDROPCOUNT_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_DROPCOUNT.
 */
struct ALT_SDR_CTL_DROPCOUNT_s
{
    uint32_t  corrdropcount :  8;  /* Dropped Auto-correction Count */
    uint32_t                : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_DROPCOUNT. */
typedef volatile struct ALT_SDR_CTL_DROPCOUNT_s  ALT_SDR_CTL_DROPCOUNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_DROPCOUNT register from the beginning of the component. */
#define ALT_SDR_CTL_DROPCOUNT_OFST        0x4c

/*
 * Register : ECC Auto-correction Dropped Address Register - dropaddr
 * 
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description                    
 * :-------|:-------|:--------|:--------------------------------
 *  [31:0] | RW     | Unknown | Dropped Auto-correction Address
 * 
 */
/*
 * Field : Dropped Auto-correction Address - corrdropaddr
 * 
 * This register gives the last address which was dropped.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_DROPADDR_CORRDROPADDR register field. */
#define ALT_SDR_CTL_DROPADDR_CORRDROPADDR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_DROPADDR_CORRDROPADDR register field. */
#define ALT_SDR_CTL_DROPADDR_CORRDROPADDR_MSB        31
/* The width in bits of the ALT_SDR_CTL_DROPADDR_CORRDROPADDR register field. */
#define ALT_SDR_CTL_DROPADDR_CORRDROPADDR_WIDTH      32
/* The mask used to set the ALT_SDR_CTL_DROPADDR_CORRDROPADDR register field value. */
#define ALT_SDR_CTL_DROPADDR_CORRDROPADDR_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDR_CTL_DROPADDR_CORRDROPADDR register field value. */
#define ALT_SDR_CTL_DROPADDR_CORRDROPADDR_CLR_MSK    0x00000000
/* The reset value of the ALT_SDR_CTL_DROPADDR_CORRDROPADDR register field is UNKNOWN. */
#define ALT_SDR_CTL_DROPADDR_CORRDROPADDR_RESET      0x0
/* Extracts the ALT_SDR_CTL_DROPADDR_CORRDROPADDR field value from a register. */
#define ALT_SDR_CTL_DROPADDR_CORRDROPADDR_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDR_CTL_DROPADDR_CORRDROPADDR register field value suitable for setting the register. */
#define ALT_SDR_CTL_DROPADDR_CORRDROPADDR_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_DROPADDR.
 */
struct ALT_SDR_CTL_DROPADDR_s
{
    uint32_t  corrdropaddr : 32;  /* Dropped Auto-correction Address */
};

/* The typedef declaration for register ALT_SDR_CTL_DROPADDR. */
typedef volatile struct ALT_SDR_CTL_DROPADDR_s  ALT_SDR_CTL_DROPADDR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_DROPADDR register from the beginning of the component. */
#define ALT_SDR_CTL_DROPADDR_OFST        0x50

/*
 * Register : Low Power Control Register - lowpwreq
 * 
 * This register instructs the controller to put the DRAM into a power down state.
 * Note that some commands are only valid for certain memory types.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description                     
 * :-------|:-------|:--------|:---------------------------------
 *  [0]    | RW     | Unknown | Deep Power Down Request         
 *  [2:1]  | RW     | Unknown | Deep Power Down Chip Select Mask
 *  [3]    | RW     | Unknown | Self-refresh Request            
 *  [5:4]  | RW     | Unknown | Self-refresh Chip Select Mask   
 *  [31:6] | ???    | 0x0     | *UNDEFINED*                     
 * 
 */
/*
 * Field : Deep Power Down Request - deeppwrdnreq
 * 
 * Write a one to this bit to request a deep power down.  This bit should only be
 * written with LPDDR2 DRAMs, DDR3 DRAMs do not support deep power down.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ register field. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ register field. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ_MSB        0
/* The width in bits of the ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ register field. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ register field value. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ register field value. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ register field is UNKNOWN. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ_RESET      0x0
/* Extracts the ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ field value from a register. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ register field value suitable for setting the register. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNREQ_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Deep Power Down Chip Select Mask - deeppwrdnmask
 * 
 * Write ones to this register to select which DRAM chip selects will be powered
 * down.  Typical usage is to set both of these bits when deeppwrdnreq is set but
 * the controller does support putting a single chip into deep power down and
 * keeping the other chip running.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK register field. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK register field. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK_MSB        2
/* The width in bits of the ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK register field. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK_WIDTH      2
/* The mask used to set the ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK register field value. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK_SET_MSK    0x00000006
/* The mask used to clear the ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK register field value. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK_CLR_MSK    0xfffffff9
/* The reset value of the ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK register field is UNKNOWN. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK_RESET      0x0
/* Extracts the ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK field value from a register. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK_GET(value) (((value) & 0x00000006) >> 1)
/* Produces a ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK register field value suitable for setting the register. */
#define ALT_SDR_CTL_LOWPWREQ_DEEPPWRDNMSK_SET(value) (((value) << 1) & 0x00000006)

/*
 * Field : Self-refresh Request - selfrshreq
 * 
 * Write a one to this bit to request the RAM be put into a self refresh state.
 * This bit is treated as a static value so the RAM will remain in self-refresh as
 * long as this register bit is set to a one.  This power down mode can be selected
 * for all DRAMs supported by the controller.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ register field. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ register field. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ_MSB        3
/* The width in bits of the ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ register field. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ register field value. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ_SET_MSK    0x00000008
/* The mask used to clear the ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ register field value. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ register field is UNKNOWN. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ_RESET      0x0
/* Extracts the ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ field value from a register. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ register field value suitable for setting the register. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRSHREQ_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Self-refresh Chip Select Mask - selfrfshmask
 * 
 * Write a one to each bit of this field to have a self refresh request apply to
 * both chips.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK register field. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK register field. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK_MSB        5
/* The width in bits of the ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK register field. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK_WIDTH      2
/* The mask used to set the ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK register field value. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK_SET_MSK    0x00000030
/* The mask used to clear the ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK register field value. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK_CLR_MSK    0xffffffcf
/* The reset value of the ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK register field is UNKNOWN. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK_RESET      0x0
/* Extracts the ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK field value from a register. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK_GET(value) (((value) & 0x00000030) >> 4)
/* Produces a ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK register field value suitable for setting the register. */
#define ALT_SDR_CTL_LOWPWREQ_SELFRFSHMSK_SET(value) (((value) << 4) & 0x00000030)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_LOWPWREQ.
 */
struct ALT_SDR_CTL_LOWPWREQ_s
{
    uint32_t  deeppwrdnreq  :  1;  /* Deep Power Down Request */
    uint32_t  deeppwrdnmask :  2;  /* Deep Power Down Chip Select Mask */
    uint32_t  selfrshreq    :  1;  /* Self-refresh Request */
    uint32_t  selfrfshmask  :  2;  /* Self-refresh Chip Select Mask */
    uint32_t                : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_LOWPWREQ. */
typedef volatile struct ALT_SDR_CTL_LOWPWREQ_s  ALT_SDR_CTL_LOWPWREQ_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_LOWPWREQ register from the beginning of the component. */
#define ALT_SDR_CTL_LOWPWREQ_OFST        0x54

/*
 * Register : Low Power Acknowledge Register - lowpwrack
 * 
 * This register gives the status of the power down commands requested by the Low
 * Power Control register.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description                
 * :-------|:-------|:--------|:----------------------------
 *  [0]    | RW     | Unknown | Deep Power Down Acknowledge
 *  [1]    | RW     | Unknown | Self-refresh Acknowledge   
 *  [31:2] | ???    | 0x0     | *UNDEFINED*                
 * 
 */
/*
 * Field : Deep Power Down Acknowledge - deeppwrdnack
 * 
 * This bit is set to a one after a deep power down has been executed
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK register field. */
#define ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK register field. */
#define ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK_MSB        0
/* The width in bits of the ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK register field. */
#define ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK register field value. */
#define ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK_SET_MSK    0x00000001
/* The mask used to clear the ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK register field value. */
#define ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK_CLR_MSK    0xfffffffe
/* The reset value of the ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK register field is UNKNOWN. */
#define ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK_RESET      0x0
/* Extracts the ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK field value from a register. */
#define ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK register field value suitable for setting the register. */
#define ALT_SDR_CTL_LOWPWRACK_DEEPPWRDNACK_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Self-refresh Acknowledge - selfrfshack
 * 
 * This bit is a one to indicate that the controller is in a self-refresh state.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK register field. */
#define ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK register field. */
#define ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK_MSB        1
/* The width in bits of the ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK register field. */
#define ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK register field value. */
#define ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK_SET_MSK    0x00000002
/* The mask used to clear the ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK register field value. */
#define ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK_CLR_MSK    0xfffffffd
/* The reset value of the ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK register field is UNKNOWN. */
#define ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK_RESET      0x0
/* Extracts the ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK field value from a register. */
#define ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK register field value suitable for setting the register. */
#define ALT_SDR_CTL_LOWPWRACK_SELFRFSHACK_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_LOWPWRACK.
 */
struct ALT_SDR_CTL_LOWPWRACK_s
{
    uint32_t  deeppwrdnack :  1;  /* Deep Power Down Acknowledge */
    uint32_t  selfrfshack  :  1;  /* Self-refresh Acknowledge */
    uint32_t               : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_LOWPWRACK. */
typedef volatile struct ALT_SDR_CTL_LOWPWRACK_s  ALT_SDR_CTL_LOWPWRACK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_LOWPWRACK register from the beginning of the component. */
#define ALT_SDR_CTL_LOWPWRACK_OFST        0x58

/*
 * Register : Static Configuration Register - staticcfg
 * 
 * This register controls configuration values which cannot be updated while
 * transactions are flowing.
 * 
 * You should write once to this register with the membl and eccen fields set to
 * your desired configuration, and then write to the register again with membl and
 * eccen and the applycfg bit set. The applycfg bit is write only.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description                
 * :-------|:-------|:--------|:----------------------------
 *  [1:0]  | RW     | Unknown | Memory Burst Length        
 *  [2]    | RW     | Unknown | Use ECC Bits As Data       
 *  [3]    | RW     | Unknown | Apply Configuration Changes
 *  [31:4] | ???    | 0x0     | *UNDEFINED*                
 * 
 */
/*
 * Field : Memory Burst Length - membl
 * 
 * This field specifies the DRAM burst length. Write the following values to set
 * the a burst length appropriate for the specific DRAM being used. &quot;00&quot;
 * for burst length 2, &quot;01&quot; for burst length 4, &quot;10&quot; for burst
 * length 8. If you set this, you must also set the membl field in the ctrlcfg
 * register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_STATICCFG_MEMBL register field. */
#define ALT_SDR_CTL_STATICCFG_MEMBL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_STATICCFG_MEMBL register field. */
#define ALT_SDR_CTL_STATICCFG_MEMBL_MSB        1
/* The width in bits of the ALT_SDR_CTL_STATICCFG_MEMBL register field. */
#define ALT_SDR_CTL_STATICCFG_MEMBL_WIDTH      2
/* The mask used to set the ALT_SDR_CTL_STATICCFG_MEMBL register field value. */
#define ALT_SDR_CTL_STATICCFG_MEMBL_SET_MSK    0x00000003
/* The mask used to clear the ALT_SDR_CTL_STATICCFG_MEMBL register field value. */
#define ALT_SDR_CTL_STATICCFG_MEMBL_CLR_MSK    0xfffffffc
/* The reset value of the ALT_SDR_CTL_STATICCFG_MEMBL register field is UNKNOWN. */
#define ALT_SDR_CTL_STATICCFG_MEMBL_RESET      0x0
/* Extracts the ALT_SDR_CTL_STATICCFG_MEMBL field value from a register. */
#define ALT_SDR_CTL_STATICCFG_MEMBL_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_SDR_CTL_STATICCFG_MEMBL register field value suitable for setting the register. */
#define ALT_SDR_CTL_STATICCFG_MEMBL_SET(value) (((value) << 0) & 0x00000003)

/*
 * Field : Use ECC Bits As Data - useeccasdata
 * 
 * This field allows the FPGA ports to directly access the extra data bits that are
 * normally used to hold the ECC code. The interface width must be set to 24 or 40
 * in the dramifwidth register. If you set this, you must clear the eccen field in
 * the ctrlcfg register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_STATICCFG_USEECCASDATA register field. */
#define ALT_SDR_CTL_STATICCFG_USEECCASDATA_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_STATICCFG_USEECCASDATA register field. */
#define ALT_SDR_CTL_STATICCFG_USEECCASDATA_MSB        2
/* The width in bits of the ALT_SDR_CTL_STATICCFG_USEECCASDATA register field. */
#define ALT_SDR_CTL_STATICCFG_USEECCASDATA_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_STATICCFG_USEECCASDATA register field value. */
#define ALT_SDR_CTL_STATICCFG_USEECCASDATA_SET_MSK    0x00000004
/* The mask used to clear the ALT_SDR_CTL_STATICCFG_USEECCASDATA register field value. */
#define ALT_SDR_CTL_STATICCFG_USEECCASDATA_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SDR_CTL_STATICCFG_USEECCASDATA register field is UNKNOWN. */
#define ALT_SDR_CTL_STATICCFG_USEECCASDATA_RESET      0x0
/* Extracts the ALT_SDR_CTL_STATICCFG_USEECCASDATA field value from a register. */
#define ALT_SDR_CTL_STATICCFG_USEECCASDATA_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SDR_CTL_STATICCFG_USEECCASDATA register field value suitable for setting the register. */
#define ALT_SDR_CTL_STATICCFG_USEECCASDATA_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Apply Configuration Changes - applycfg
 * 
 * Write with this bit set to apply all the settings loaded in SDR registers to the
 * memory interface. This bit is write-only and always returns 0 if read.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_STATICCFG_APPLYCFG register field. */
#define ALT_SDR_CTL_STATICCFG_APPLYCFG_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_STATICCFG_APPLYCFG register field. */
#define ALT_SDR_CTL_STATICCFG_APPLYCFG_MSB        3
/* The width in bits of the ALT_SDR_CTL_STATICCFG_APPLYCFG register field. */
#define ALT_SDR_CTL_STATICCFG_APPLYCFG_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_STATICCFG_APPLYCFG register field value. */
#define ALT_SDR_CTL_STATICCFG_APPLYCFG_SET_MSK    0x00000008
/* The mask used to clear the ALT_SDR_CTL_STATICCFG_APPLYCFG register field value. */
#define ALT_SDR_CTL_STATICCFG_APPLYCFG_CLR_MSK    0xfffffff7
/* The reset value of the ALT_SDR_CTL_STATICCFG_APPLYCFG register field is UNKNOWN. */
#define ALT_SDR_CTL_STATICCFG_APPLYCFG_RESET      0x0
/* Extracts the ALT_SDR_CTL_STATICCFG_APPLYCFG field value from a register. */
#define ALT_SDR_CTL_STATICCFG_APPLYCFG_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_SDR_CTL_STATICCFG_APPLYCFG register field value suitable for setting the register. */
#define ALT_SDR_CTL_STATICCFG_APPLYCFG_SET(value) (((value) << 3) & 0x00000008)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_STATICCFG.
 */
struct ALT_SDR_CTL_STATICCFG_s
{
    uint32_t  membl        :  2;  /* Memory Burst Length */
    uint32_t  useeccasdata :  1;  /* Use ECC Bits As Data */
    uint32_t  applycfg     :  1;  /* Apply Configuration Changes */
    uint32_t               : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_STATICCFG. */
typedef volatile struct ALT_SDR_CTL_STATICCFG_s  ALT_SDR_CTL_STATICCFG_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_STATICCFG register from the beginning of the component. */
#define ALT_SDR_CTL_STATICCFG_OFST        0x5c

/*
 * Register : Memory Controller Width Register - ctrlwidth
 * 
 * This register controls the width of the physical DRAM interface.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description               
 * :-------|:-------|:--------|:---------------------------
 *  [1:0]  | RW     | Unknown | Controller Interface Width
 *  [31:2] | ???    | 0x0     | *UNDEFINED*               
 * 
 */
/*
 * Field : Controller Interface Width - ctrlwidth
 * 
 * Specifies controller DRAM interface width, with the following encoding.
 * &quot;00&quot; for 8-bit, &quot;01&quot; for 16-bit (no ECC) or 24-bit (ECC
 * enabled), &quot;10&quot; for 32-bit (no ECC) or 40-bit (ECC enabled). You must
 * also program the dramifwidth register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_CTLWIDTH_CTLWIDTH register field. */
#define ALT_SDR_CTL_CTLWIDTH_CTLWIDTH_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_CTLWIDTH_CTLWIDTH register field. */
#define ALT_SDR_CTL_CTLWIDTH_CTLWIDTH_MSB        1
/* The width in bits of the ALT_SDR_CTL_CTLWIDTH_CTLWIDTH register field. */
#define ALT_SDR_CTL_CTLWIDTH_CTLWIDTH_WIDTH      2
/* The mask used to set the ALT_SDR_CTL_CTLWIDTH_CTLWIDTH register field value. */
#define ALT_SDR_CTL_CTLWIDTH_CTLWIDTH_SET_MSK    0x00000003
/* The mask used to clear the ALT_SDR_CTL_CTLWIDTH_CTLWIDTH register field value. */
#define ALT_SDR_CTL_CTLWIDTH_CTLWIDTH_CLR_MSK    0xfffffffc
/* The reset value of the ALT_SDR_CTL_CTLWIDTH_CTLWIDTH register field is UNKNOWN. */
#define ALT_SDR_CTL_CTLWIDTH_CTLWIDTH_RESET      0x0
/* Extracts the ALT_SDR_CTL_CTLWIDTH_CTLWIDTH field value from a register. */
#define ALT_SDR_CTL_CTLWIDTH_CTLWIDTH_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_SDR_CTL_CTLWIDTH_CTLWIDTH register field value suitable for setting the register. */
#define ALT_SDR_CTL_CTLWIDTH_CTLWIDTH_SET(value) (((value) << 0) & 0x00000003)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_CTLWIDTH.
 */
struct ALT_SDR_CTL_CTLWIDTH_s
{
    uint32_t  ctrlwidth :  2;  /* Controller Interface Width */
    uint32_t            : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_CTLWIDTH. */
typedef volatile struct ALT_SDR_CTL_CTLWIDTH_s  ALT_SDR_CTL_CTLWIDTH_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_CTLWIDTH register from the beginning of the component. */
#define ALT_SDR_CTL_CTLWIDTH_OFST        0x60

/*
 * Register : Port Configuration Register - portcfg
 * 
 * This register should be set to a zero in any bit which corresponds to a port
 * which does mostly sequential memory accesses.  For ports with highly random
 * accesses, the bit should be set to a one.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description          
 * :--------|:-------|:--------|:----------------------
 *  [9:0]   | ???    | Unknown | *UNDEFINED*          
 *  [19:10] | RW     | Unknown | Auto-precharge Enable
 *  [31:20] | ???    | 0x0     | *UNDEFINED*          
 * 
 */
/*
 * Field : Auto-precharge Enable - autopchen
 * 
 * One bit per control port.  Set bit N to a 1 to have the controller request an
 * automatic precharge following bus command completion (close the row
 * automatically).  Set to a zero to request that the controller attempt to keep a
 * row open.  For random dominated operations this register should be set to a 1
 * for all active ports.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_PORTCFG_AUTOPCHEN register field. */
#define ALT_SDR_CTL_PORTCFG_AUTOPCHEN_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_PORTCFG_AUTOPCHEN register field. */
#define ALT_SDR_CTL_PORTCFG_AUTOPCHEN_MSB        19
/* The width in bits of the ALT_SDR_CTL_PORTCFG_AUTOPCHEN register field. */
#define ALT_SDR_CTL_PORTCFG_AUTOPCHEN_WIDTH      10
/* The mask used to set the ALT_SDR_CTL_PORTCFG_AUTOPCHEN register field value. */
#define ALT_SDR_CTL_PORTCFG_AUTOPCHEN_SET_MSK    0x000ffc00
/* The mask used to clear the ALT_SDR_CTL_PORTCFG_AUTOPCHEN register field value. */
#define ALT_SDR_CTL_PORTCFG_AUTOPCHEN_CLR_MSK    0xfff003ff
/* The reset value of the ALT_SDR_CTL_PORTCFG_AUTOPCHEN register field is UNKNOWN. */
#define ALT_SDR_CTL_PORTCFG_AUTOPCHEN_RESET      0x0
/* Extracts the ALT_SDR_CTL_PORTCFG_AUTOPCHEN field value from a register. */
#define ALT_SDR_CTL_PORTCFG_AUTOPCHEN_GET(value) (((value) & 0x000ffc00) >> 10)
/* Produces a ALT_SDR_CTL_PORTCFG_AUTOPCHEN register field value suitable for setting the register. */
#define ALT_SDR_CTL_PORTCFG_AUTOPCHEN_SET(value) (((value) << 10) & 0x000ffc00)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_PORTCFG.
 */
struct ALT_SDR_CTL_PORTCFG_s
{
    uint32_t            : 10;  /* *UNDEFINED* */
    uint32_t  autopchen : 10;  /* Auto-precharge Enable */
    uint32_t            : 12;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_PORTCFG. */
typedef volatile struct ALT_SDR_CTL_PORTCFG_s  ALT_SDR_CTL_PORTCFG_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_PORTCFG register from the beginning of the component. */
#define ALT_SDR_CTL_PORTCFG_OFST        0x7c

/*
 * Register : FPGA Ports Reset Control Register - fpgaportrst
 * 
 * This register implements functionality to allow the CPU to control when the MPFE
 * will enable the ports to the FPGA fabric.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description       
 * :--------|:-------|:--------|:-------------------
 *  [13:0]  | RW     | Unknown | Port Reset Control
 *  [31:14] | ???    | 0x0     | *UNDEFINED*       
 * 
 */
/*
 * Field : Port Reset Control - portrstn
 * 
 * This register should be written to with a 1 to enable the selected FPGA port to
 * exit reset.  Writing a bit to a zero will stretch the port reset until the
 * register is written. Read data ports are connected to bits 3:0, with read data
 * port 0 at bit 0 to read data port 3 at bit 3. Write data ports 0 to 3 are mapped
 * to 4 to 7, with write data port 0 connected to bit 4 to write data port 3 at bit
 * 7. Command ports are connected to bits 8 to 13, with command port 0 at bit 8 to
 * command port 5 at bit 13. Expected usage would be to set all the bits at the
 * same time but setting some bits to a zero and others to a one is supported.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_FPGAPORTRST_PORTRSTN register field. */
#define ALT_SDR_CTL_FPGAPORTRST_PORTRSTN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_FPGAPORTRST_PORTRSTN register field. */
#define ALT_SDR_CTL_FPGAPORTRST_PORTRSTN_MSB        13
/* The width in bits of the ALT_SDR_CTL_FPGAPORTRST_PORTRSTN register field. */
#define ALT_SDR_CTL_FPGAPORTRST_PORTRSTN_WIDTH      14
/* The mask used to set the ALT_SDR_CTL_FPGAPORTRST_PORTRSTN register field value. */
#define ALT_SDR_CTL_FPGAPORTRST_PORTRSTN_SET_MSK    0x00003fff
/* The mask used to clear the ALT_SDR_CTL_FPGAPORTRST_PORTRSTN register field value. */
#define ALT_SDR_CTL_FPGAPORTRST_PORTRSTN_CLR_MSK    0xffffc000
/* The reset value of the ALT_SDR_CTL_FPGAPORTRST_PORTRSTN register field is UNKNOWN. */
#define ALT_SDR_CTL_FPGAPORTRST_PORTRSTN_RESET      0x0
/* Extracts the ALT_SDR_CTL_FPGAPORTRST_PORTRSTN field value from a register. */
#define ALT_SDR_CTL_FPGAPORTRST_PORTRSTN_GET(value) (((value) & 0x00003fff) >> 0)
/* Produces a ALT_SDR_CTL_FPGAPORTRST_PORTRSTN register field value suitable for setting the register. */
#define ALT_SDR_CTL_FPGAPORTRST_PORTRSTN_SET(value) (((value) << 0) & 0x00003fff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_FPGAPORTRST.
 */
struct ALT_SDR_CTL_FPGAPORTRST_s
{
    uint32_t  portrstn : 14;  /* Port Reset Control */
    uint32_t           : 18;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_FPGAPORTRST. */
typedef volatile struct ALT_SDR_CTL_FPGAPORTRST_s  ALT_SDR_CTL_FPGAPORTRST_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_FPGAPORTRST register from the beginning of the component. */
#define ALT_SDR_CTL_FPGAPORTRST_OFST        0x80

/*
 * Register : Memory Protection Port Default Register - protportdefault
 * 
 * This register controls the default protection assignment for a port.  Ports
 * which have explicit rules which define regions which are illegal to access
 * should set the bits to pass by default.  Ports which have explicit rules which
 * define legal areas should set the bit to force all transactions to fail.
 * Leaving this register to all zeros should be used for systems which do not
 * desire any protection from the memory controller.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description        
 * :--------|:-------|:--------|:--------------------
 *  [9:0]   | RW     | Unknown | Port Default Action
 *  [31:10] | ???    | 0x0     | *UNDEFINED*        
 * 
 */
/*
 * Field : Port Default Action - portdefault
 * 
 * Determines the default action for a transactions from a port.  Set a bit to a
 * zero to indicate that all accesses from the port should pass by default, set a
 * bit to a one if the default protection is to fail the access.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT register field. */
#define ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT register field. */
#define ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT_MSB        9
/* The width in bits of the ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT register field. */
#define ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT_WIDTH      10
/* The mask used to set the ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT register field value. */
#define ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT_SET_MSK    0x000003ff
/* The mask used to clear the ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT register field value. */
#define ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT_CLR_MSK    0xfffffc00
/* The reset value of the ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT register field is UNKNOWN. */
#define ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT_RESET      0x0
/* Extracts the ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT field value from a register. */
#define ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT_GET(value) (((value) & 0x000003ff) >> 0)
/* Produces a ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT register field value suitable for setting the register. */
#define ALT_SDR_CTL_PROTPORTDEFAULT_PORTDEFAULT_SET(value) (((value) << 0) & 0x000003ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_PROTPORTDEFAULT.
 */
struct ALT_SDR_CTL_PROTPORTDEFAULT_s
{
    uint32_t  portdefault : 10;  /* Port Default Action */
    uint32_t              : 22;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_PROTPORTDEFAULT. */
typedef volatile struct ALT_SDR_CTL_PROTPORTDEFAULT_s  ALT_SDR_CTL_PROTPORTDEFAULT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_PROTPORTDEFAULT register from the beginning of the component. */
#define ALT_SDR_CTL_PROTPORTDEFAULT_OFST        0x8c

/*
 * Register : Memory Protection Address Register - protruleaddr
 * 
 * This register is used to control the memory protection for port 0 transactions.
 * Address ranges can either be used to allow access to memory regions or disallow
 * access to memory regions.  If trustzone is being used, access can be enabled for
 * protected transactions or disabled for unprotected transactions.  The default
 * state of this register is to allow all access.  Address values used for
 * protection are only physical addresses.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description 
 * :--------|:-------|:--------|:-------------
 *  [11:0]  | RW     | Unknown | Low Address 
 *  [23:12] | RW     | Unknown | High Address
 *  [31:24] | ???    | 0x0     | *UNDEFINED* 
 * 
 */
/*
 * Field : Low Address - lowaddr
 * 
 * Lower 12 bits of the address for a check.  Address is compared to be less than
 * or equal to the address of a transaction.  Note that since AXI transactions
 * cannot cross a 4K byte boundary, the transaction start and transaction end
 * address must also fall within the same 1MByte block pointed to by this address
 * pointer.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_PROTRULEADDR_LOWADDR register field. */
#define ALT_SDR_CTL_PROTRULEADDR_LOWADDR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_PROTRULEADDR_LOWADDR register field. */
#define ALT_SDR_CTL_PROTRULEADDR_LOWADDR_MSB        11
/* The width in bits of the ALT_SDR_CTL_PROTRULEADDR_LOWADDR register field. */
#define ALT_SDR_CTL_PROTRULEADDR_LOWADDR_WIDTH      12
/* The mask used to set the ALT_SDR_CTL_PROTRULEADDR_LOWADDR register field value. */
#define ALT_SDR_CTL_PROTRULEADDR_LOWADDR_SET_MSK    0x00000fff
/* The mask used to clear the ALT_SDR_CTL_PROTRULEADDR_LOWADDR register field value. */
#define ALT_SDR_CTL_PROTRULEADDR_LOWADDR_CLR_MSK    0xfffff000
/* The reset value of the ALT_SDR_CTL_PROTRULEADDR_LOWADDR register field is UNKNOWN. */
#define ALT_SDR_CTL_PROTRULEADDR_LOWADDR_RESET      0x0
/* Extracts the ALT_SDR_CTL_PROTRULEADDR_LOWADDR field value from a register. */
#define ALT_SDR_CTL_PROTRULEADDR_LOWADDR_GET(value) (((value) & 0x00000fff) >> 0)
/* Produces a ALT_SDR_CTL_PROTRULEADDR_LOWADDR register field value suitable for setting the register. */
#define ALT_SDR_CTL_PROTRULEADDR_LOWADDR_SET(value) (((value) << 0) & 0x00000fff)

/*
 * Field : High Address - highaddr
 * 
 * Upper 12 bits of the address for a check.  Address is compared to be greater
 * than or equal to the address of a transaction.  Note that since AXI transactions
 * cannot cross a 4K byte boundary, the transaction start and transaction end
 * address must also fall within the same 1MByte block pointed to by this address
 * pointer.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_PROTRULEADDR_HIGHADDR register field. */
#define ALT_SDR_CTL_PROTRULEADDR_HIGHADDR_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_PROTRULEADDR_HIGHADDR register field. */
#define ALT_SDR_CTL_PROTRULEADDR_HIGHADDR_MSB        23
/* The width in bits of the ALT_SDR_CTL_PROTRULEADDR_HIGHADDR register field. */
#define ALT_SDR_CTL_PROTRULEADDR_HIGHADDR_WIDTH      12
/* The mask used to set the ALT_SDR_CTL_PROTRULEADDR_HIGHADDR register field value. */
#define ALT_SDR_CTL_PROTRULEADDR_HIGHADDR_SET_MSK    0x00fff000
/* The mask used to clear the ALT_SDR_CTL_PROTRULEADDR_HIGHADDR register field value. */
#define ALT_SDR_CTL_PROTRULEADDR_HIGHADDR_CLR_MSK    0xff000fff
/* The reset value of the ALT_SDR_CTL_PROTRULEADDR_HIGHADDR register field is UNKNOWN. */
#define ALT_SDR_CTL_PROTRULEADDR_HIGHADDR_RESET      0x0
/* Extracts the ALT_SDR_CTL_PROTRULEADDR_HIGHADDR field value from a register. */
#define ALT_SDR_CTL_PROTRULEADDR_HIGHADDR_GET(value) (((value) & 0x00fff000) >> 12)
/* Produces a ALT_SDR_CTL_PROTRULEADDR_HIGHADDR register field value suitable for setting the register. */
#define ALT_SDR_CTL_PROTRULEADDR_HIGHADDR_SET(value) (((value) << 12) & 0x00fff000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_PROTRULEADDR.
 */
struct ALT_SDR_CTL_PROTRULEADDR_s
{
    uint32_t  lowaddr  : 12;  /* Low Address */
    uint32_t  highaddr : 12;  /* High Address */
    uint32_t           :  8;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_PROTRULEADDR. */
typedef volatile struct ALT_SDR_CTL_PROTRULEADDR_s  ALT_SDR_CTL_PROTRULEADDR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_PROTRULEADDR register from the beginning of the component. */
#define ALT_SDR_CTL_PROTRULEADDR_OFST        0x90

/*
 * Register : Memory Protection ID Register - protruleid
 * 
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description
 * :--------|:-------|:--------|:------------
 *  [11:0]  | RW     | Unknown | Low ID     
 *  [23:12] | RW     | Unknown | High ID    
 *  [31:24] | ???    | 0x0     | *UNDEFINED*
 * 
 */
/*
 * Field : Low ID - lowid
 * 
 * AxID for the protection rule.  Incoming AxID needs to be greater than or equal
 * to this value.  For all AxIDs from a port, AxID high should be programmed to all
 * ones.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_PROTRULEID_LOWID register field. */
#define ALT_SDR_CTL_PROTRULEID_LOWID_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_PROTRULEID_LOWID register field. */
#define ALT_SDR_CTL_PROTRULEID_LOWID_MSB        11
/* The width in bits of the ALT_SDR_CTL_PROTRULEID_LOWID register field. */
#define ALT_SDR_CTL_PROTRULEID_LOWID_WIDTH      12
/* The mask used to set the ALT_SDR_CTL_PROTRULEID_LOWID register field value. */
#define ALT_SDR_CTL_PROTRULEID_LOWID_SET_MSK    0x00000fff
/* The mask used to clear the ALT_SDR_CTL_PROTRULEID_LOWID register field value. */
#define ALT_SDR_CTL_PROTRULEID_LOWID_CLR_MSK    0xfffff000
/* The reset value of the ALT_SDR_CTL_PROTRULEID_LOWID register field is UNKNOWN. */
#define ALT_SDR_CTL_PROTRULEID_LOWID_RESET      0x0
/* Extracts the ALT_SDR_CTL_PROTRULEID_LOWID field value from a register. */
#define ALT_SDR_CTL_PROTRULEID_LOWID_GET(value) (((value) & 0x00000fff) >> 0)
/* Produces a ALT_SDR_CTL_PROTRULEID_LOWID register field value suitable for setting the register. */
#define ALT_SDR_CTL_PROTRULEID_LOWID_SET(value) (((value) << 0) & 0x00000fff)

/*
 * Field : High ID - highid
 * 
 * AxID for the protection rule.  Incoming AxID needs to be less than or equal to
 * this value.  For all AxIDs from a port, AxID high should be programmed to all
 * ones.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_PROTRULEID_HIGHID register field. */
#define ALT_SDR_CTL_PROTRULEID_HIGHID_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_PROTRULEID_HIGHID register field. */
#define ALT_SDR_CTL_PROTRULEID_HIGHID_MSB        23
/* The width in bits of the ALT_SDR_CTL_PROTRULEID_HIGHID register field. */
#define ALT_SDR_CTL_PROTRULEID_HIGHID_WIDTH      12
/* The mask used to set the ALT_SDR_CTL_PROTRULEID_HIGHID register field value. */
#define ALT_SDR_CTL_PROTRULEID_HIGHID_SET_MSK    0x00fff000
/* The mask used to clear the ALT_SDR_CTL_PROTRULEID_HIGHID register field value. */
#define ALT_SDR_CTL_PROTRULEID_HIGHID_CLR_MSK    0xff000fff
/* The reset value of the ALT_SDR_CTL_PROTRULEID_HIGHID register field is UNKNOWN. */
#define ALT_SDR_CTL_PROTRULEID_HIGHID_RESET      0x0
/* Extracts the ALT_SDR_CTL_PROTRULEID_HIGHID field value from a register. */
#define ALT_SDR_CTL_PROTRULEID_HIGHID_GET(value) (((value) & 0x00fff000) >> 12)
/* Produces a ALT_SDR_CTL_PROTRULEID_HIGHID register field value suitable for setting the register. */
#define ALT_SDR_CTL_PROTRULEID_HIGHID_SET(value) (((value) << 12) & 0x00fff000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_PROTRULEID.
 */
struct ALT_SDR_CTL_PROTRULEID_s
{
    uint32_t  lowid  : 12;  /* Low ID */
    uint32_t  highid : 12;  /* High ID */
    uint32_t         :  8;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_PROTRULEID. */
typedef volatile struct ALT_SDR_CTL_PROTRULEID_s  ALT_SDR_CTL_PROTRULEID_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_PROTRULEID register from the beginning of the component. */
#define ALT_SDR_CTL_PROTRULEID_OFST        0x94

/*
 * Register : Memory Protection Rule Data Register - protruledata
 * 
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description          
 * :--------|:-------|:--------|:----------------------
 *  [1:0]   | RW     | Unknown | Security Bit Behavior
 *  [2]     | RW     | Unknown | Valid Rule           
 *  [12:3]  | RW     | Unknown | Port Mask            
 *  [13]    | RW     | Unknown | Rule Results         
 *  [31:14] | ???    | 0x0     | *UNDEFINED*          
 * 
 */
/*
 * Field : Security Bit Behavior - security
 * 
 * A value of 2'b00 will make the rule apply to secure transactions.
 * 
 * A value of 2'b01 will make the rule apply to non-secure transactions.
 * 
 * A value of 2'b10 or 2'b11 will make the rule apply to secure and non-secure
 * transactions.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_PROTRULEDATA_SECURITY register field. */
#define ALT_SDR_CTL_PROTRULEDATA_SECURITY_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_PROTRULEDATA_SECURITY register field. */
#define ALT_SDR_CTL_PROTRULEDATA_SECURITY_MSB        1
/* The width in bits of the ALT_SDR_CTL_PROTRULEDATA_SECURITY register field. */
#define ALT_SDR_CTL_PROTRULEDATA_SECURITY_WIDTH      2
/* The mask used to set the ALT_SDR_CTL_PROTRULEDATA_SECURITY register field value. */
#define ALT_SDR_CTL_PROTRULEDATA_SECURITY_SET_MSK    0x00000003
/* The mask used to clear the ALT_SDR_CTL_PROTRULEDATA_SECURITY register field value. */
#define ALT_SDR_CTL_PROTRULEDATA_SECURITY_CLR_MSK    0xfffffffc
/* The reset value of the ALT_SDR_CTL_PROTRULEDATA_SECURITY register field is UNKNOWN. */
#define ALT_SDR_CTL_PROTRULEDATA_SECURITY_RESET      0x0
/* Extracts the ALT_SDR_CTL_PROTRULEDATA_SECURITY field value from a register. */
#define ALT_SDR_CTL_PROTRULEDATA_SECURITY_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_SDR_CTL_PROTRULEDATA_SECURITY register field value suitable for setting the register. */
#define ALT_SDR_CTL_PROTRULEDATA_SECURITY_SET(value) (((value) << 0) & 0x00000003)

/*
 * Field : Valid Rule - validrule
 * 
 * Set to bit to a one to make a rule valid, set to a zero to invalidate a rule.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_PROTRULEDATA_VALIDRULE register field. */
#define ALT_SDR_CTL_PROTRULEDATA_VALIDRULE_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_PROTRULEDATA_VALIDRULE register field. */
#define ALT_SDR_CTL_PROTRULEDATA_VALIDRULE_MSB        2
/* The width in bits of the ALT_SDR_CTL_PROTRULEDATA_VALIDRULE register field. */
#define ALT_SDR_CTL_PROTRULEDATA_VALIDRULE_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_PROTRULEDATA_VALIDRULE register field value. */
#define ALT_SDR_CTL_PROTRULEDATA_VALIDRULE_SET_MSK    0x00000004
/* The mask used to clear the ALT_SDR_CTL_PROTRULEDATA_VALIDRULE register field value. */
#define ALT_SDR_CTL_PROTRULEDATA_VALIDRULE_CLR_MSK    0xfffffffb
/* The reset value of the ALT_SDR_CTL_PROTRULEDATA_VALIDRULE register field is UNKNOWN. */
#define ALT_SDR_CTL_PROTRULEDATA_VALIDRULE_RESET      0x0
/* Extracts the ALT_SDR_CTL_PROTRULEDATA_VALIDRULE field value from a register. */
#define ALT_SDR_CTL_PROTRULEDATA_VALIDRULE_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_SDR_CTL_PROTRULEDATA_VALIDRULE register field value suitable for setting the register. */
#define ALT_SDR_CTL_PROTRULEDATA_VALIDRULE_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Port Mask - portmask
 * 
 * Set  bit x to a one to have this rule apply to port x, set bit x to a zero to
 * have the rule not apply to a port.&#10;Note that port 0-port 5 are the FPGA
 * fabric ports, port 6 is L3 read, port 7 is CPU read, port 8 is L3 write, port 9
 * is CPU write.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_PROTRULEDATA_PORTMSK register field. */
#define ALT_SDR_CTL_PROTRULEDATA_PORTMSK_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_PROTRULEDATA_PORTMSK register field. */
#define ALT_SDR_CTL_PROTRULEDATA_PORTMSK_MSB        12
/* The width in bits of the ALT_SDR_CTL_PROTRULEDATA_PORTMSK register field. */
#define ALT_SDR_CTL_PROTRULEDATA_PORTMSK_WIDTH      10
/* The mask used to set the ALT_SDR_CTL_PROTRULEDATA_PORTMSK register field value. */
#define ALT_SDR_CTL_PROTRULEDATA_PORTMSK_SET_MSK    0x00001ff8
/* The mask used to clear the ALT_SDR_CTL_PROTRULEDATA_PORTMSK register field value. */
#define ALT_SDR_CTL_PROTRULEDATA_PORTMSK_CLR_MSK    0xffffe007
/* The reset value of the ALT_SDR_CTL_PROTRULEDATA_PORTMSK register field is UNKNOWN. */
#define ALT_SDR_CTL_PROTRULEDATA_PORTMSK_RESET      0x0
/* Extracts the ALT_SDR_CTL_PROTRULEDATA_PORTMSK field value from a register. */
#define ALT_SDR_CTL_PROTRULEDATA_PORTMSK_GET(value) (((value) & 0x00001ff8) >> 3)
/* Produces a ALT_SDR_CTL_PROTRULEDATA_PORTMSK register field value suitable for setting the register. */
#define ALT_SDR_CTL_PROTRULEDATA_PORTMSK_SET(value) (((value) << 3) & 0x00001ff8)

/*
 * Field : Rule Results - ruleresult
 * 
 * Set this bit to a one to force a protection failure, zero to allow the access
 * the succeed
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_PROTRULEDATA_RULERESULT register field. */
#define ALT_SDR_CTL_PROTRULEDATA_RULERESULT_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_PROTRULEDATA_RULERESULT register field. */
#define ALT_SDR_CTL_PROTRULEDATA_RULERESULT_MSB        13
/* The width in bits of the ALT_SDR_CTL_PROTRULEDATA_RULERESULT register field. */
#define ALT_SDR_CTL_PROTRULEDATA_RULERESULT_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_PROTRULEDATA_RULERESULT register field value. */
#define ALT_SDR_CTL_PROTRULEDATA_RULERESULT_SET_MSK    0x00002000
/* The mask used to clear the ALT_SDR_CTL_PROTRULEDATA_RULERESULT register field value. */
#define ALT_SDR_CTL_PROTRULEDATA_RULERESULT_CLR_MSK    0xffffdfff
/* The reset value of the ALT_SDR_CTL_PROTRULEDATA_RULERESULT register field is UNKNOWN. */
#define ALT_SDR_CTL_PROTRULEDATA_RULERESULT_RESET      0x0
/* Extracts the ALT_SDR_CTL_PROTRULEDATA_RULERESULT field value from a register. */
#define ALT_SDR_CTL_PROTRULEDATA_RULERESULT_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_SDR_CTL_PROTRULEDATA_RULERESULT register field value suitable for setting the register. */
#define ALT_SDR_CTL_PROTRULEDATA_RULERESULT_SET(value) (((value) << 13) & 0x00002000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_PROTRULEDATA.
 */
struct ALT_SDR_CTL_PROTRULEDATA_s
{
    uint32_t  security   :  2;  /* Security Bit Behavior */
    uint32_t  validrule  :  1;  /* Valid Rule */
    uint32_t  portmask   : 10;  /* Port Mask */
    uint32_t  ruleresult :  1;  /* Rule Results */
    uint32_t             : 18;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_PROTRULEDATA. */
typedef volatile struct ALT_SDR_CTL_PROTRULEDATA_s  ALT_SDR_CTL_PROTRULEDATA_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_PROTRULEDATA register from the beginning of the component. */
#define ALT_SDR_CTL_PROTRULEDATA_OFST        0x98

/*
 * Register : Memory Protection Rule Read-Write Register - protrulerdwr
 * 
 * This register is used to perform read and write operations to the internal
 * protection table.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description
 * :-------|:-------|:--------|:------------
 *  [4:0]  | RW     | Unknown | Rule Offset
 *  [5]    | RW     | Unknown | Rule Write 
 *  [6]    | RW     | Unknown | Rule Read  
 *  [31:7] | ???    | 0x0     | *UNDEFINED*
 * 
 */
/*
 * Field : Rule Offset - ruleoffset
 * 
 * This field defines which of the 20 rules in the protection table you want to
 * read or write.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET register field. */
#define ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET register field. */
#define ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET_MSB        4
/* The width in bits of the ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET register field. */
#define ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET_WIDTH      5
/* The mask used to set the ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET register field value. */
#define ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET_SET_MSK    0x0000001f
/* The mask used to clear the ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET register field value. */
#define ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET_CLR_MSK    0xffffffe0
/* The reset value of the ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET register field is UNKNOWN. */
#define ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET_RESET      0x0
/* Extracts the ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET field value from a register. */
#define ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET_GET(value) (((value) & 0x0000001f) >> 0)
/* Produces a ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET register field value suitable for setting the register. */
#define ALT_SDR_CTL_PROTRULERDWR_RULEOFFSET_SET(value) (((value) << 0) & 0x0000001f)

/*
 * Field : Rule Write - writerule
 * 
 * Write to this bit to have the memory_prot_data register to the table at the
 * offset specified by port_offset.  Bit automatically clears after a single cycle
 * and the write operation is complete.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_PROTRULERDWR_WRRULE register field. */
#define ALT_SDR_CTL_PROTRULERDWR_WRRULE_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_PROTRULERDWR_WRRULE register field. */
#define ALT_SDR_CTL_PROTRULERDWR_WRRULE_MSB        5
/* The width in bits of the ALT_SDR_CTL_PROTRULERDWR_WRRULE register field. */
#define ALT_SDR_CTL_PROTRULERDWR_WRRULE_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_PROTRULERDWR_WRRULE register field value. */
#define ALT_SDR_CTL_PROTRULERDWR_WRRULE_SET_MSK    0x00000020
/* The mask used to clear the ALT_SDR_CTL_PROTRULERDWR_WRRULE register field value. */
#define ALT_SDR_CTL_PROTRULERDWR_WRRULE_CLR_MSK    0xffffffdf
/* The reset value of the ALT_SDR_CTL_PROTRULERDWR_WRRULE register field is UNKNOWN. */
#define ALT_SDR_CTL_PROTRULERDWR_WRRULE_RESET      0x0
/* Extracts the ALT_SDR_CTL_PROTRULERDWR_WRRULE field value from a register. */
#define ALT_SDR_CTL_PROTRULERDWR_WRRULE_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_SDR_CTL_PROTRULERDWR_WRRULE register field value suitable for setting the register. */
#define ALT_SDR_CTL_PROTRULERDWR_WRRULE_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Rule Read - readrule
 * 
 * Write to this bit to have the memory_prot_data register loaded with the value
 * from the internal protection table at offset.  Table value will be loaded before
 * a rdy is returned so read data from the register will be correct for any follow-
 * on reads to the memory_prot_data register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_PROTRULERDWR_RDRULE register field. */
#define ALT_SDR_CTL_PROTRULERDWR_RDRULE_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_PROTRULERDWR_RDRULE register field. */
#define ALT_SDR_CTL_PROTRULERDWR_RDRULE_MSB        6
/* The width in bits of the ALT_SDR_CTL_PROTRULERDWR_RDRULE register field. */
#define ALT_SDR_CTL_PROTRULERDWR_RDRULE_WIDTH      1
/* The mask used to set the ALT_SDR_CTL_PROTRULERDWR_RDRULE register field value. */
#define ALT_SDR_CTL_PROTRULERDWR_RDRULE_SET_MSK    0x00000040
/* The mask used to clear the ALT_SDR_CTL_PROTRULERDWR_RDRULE register field value. */
#define ALT_SDR_CTL_PROTRULERDWR_RDRULE_CLR_MSK    0xffffffbf
/* The reset value of the ALT_SDR_CTL_PROTRULERDWR_RDRULE register field is UNKNOWN. */
#define ALT_SDR_CTL_PROTRULERDWR_RDRULE_RESET      0x0
/* Extracts the ALT_SDR_CTL_PROTRULERDWR_RDRULE field value from a register. */
#define ALT_SDR_CTL_PROTRULERDWR_RDRULE_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_SDR_CTL_PROTRULERDWR_RDRULE register field value suitable for setting the register. */
#define ALT_SDR_CTL_PROTRULERDWR_RDRULE_SET(value) (((value) << 6) & 0x00000040)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_PROTRULERDWR.
 */
struct ALT_SDR_CTL_PROTRULERDWR_s
{
    uint32_t  ruleoffset :  5;  /* Rule Offset */
    uint32_t  writerule  :  1;  /* Rule Write */
    uint32_t  readrule   :  1;  /* Rule Read */
    uint32_t             : 25;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_PROTRULERDWR. */
typedef volatile struct ALT_SDR_CTL_PROTRULERDWR_s  ALT_SDR_CTL_PROTRULERDWR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_PROTRULERDWR register from the beginning of the component. */
#define ALT_SDR_CTL_PROTRULERDWR_OFST        0x9c

/*
 * Register : QOS Control Register - qoslowpri
 * 
 * This register controls the mapping of AXI4 QOS received from the FPGA fabric to
 * the internal priority used for traffic prioritization.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description           
 * :--------|:-------|:--------|:-----------------------
 *  [19:0]  | RW     | Unknown | Low Priority QoS Value
 *  [31:20] | ???    | 0x0     | *UNDEFINED*           
 * 
 */
/*
 * Field : Low Priority QoS Value - lowpriorityval
 * 
 * This 20 bit field is a 2 bit field for each of the 10 ports.  The field used for
 * each port in this register controls the priority used for a port
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL register field. */
#define ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL register field. */
#define ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL_MSB        19
/* The width in bits of the ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL register field. */
#define ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL_WIDTH      20
/* The mask used to set the ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL register field value. */
#define ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL_SET_MSK    0x000fffff
/* The mask used to clear the ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL register field value. */
#define ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL_CLR_MSK    0xfff00000
/* The reset value of the ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL register field is UNKNOWN. */
#define ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL_RESET      0x0
/* Extracts the ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL field value from a register. */
#define ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL_GET(value) (((value) & 0x000fffff) >> 0)
/* Produces a ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL register field value suitable for setting the register. */
#define ALT_SDR_CTL_QOSLOWPRI_LOWPRIORITYVAL_SET(value) (((value) << 0) & 0x000fffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_QOSLOWPRI.
 */
struct ALT_SDR_CTL_QOSLOWPRI_s
{
    uint32_t  lowpriorityval : 20;  /* Low Priority QoS Value */
    uint32_t                 : 12;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_QOSLOWPRI. */
typedef volatile struct ALT_SDR_CTL_QOSLOWPRI_s  ALT_SDR_CTL_QOSLOWPRI_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_QOSLOWPRI register from the beginning of the component. */
#define ALT_SDR_CTL_QOSLOWPRI_OFST        0xa0

/*
 * Register : qoshighpri Register - qoshighpri
 * 
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description            
 * :--------|:-------|:--------|:------------------------
 *  [19:0]  | RW     | Unknown | High Priority QoS Value
 *  [31:20] | ???    | 0x0     | *UNDEFINED*            
 * 
 */
/*
 * Field : High Priority QoS Value - highpriorityval
 * 
 * This 20 bit field is a 2 bit field for each of the 10 ports.  The field used for
 * each port in this register controls the priority used for a port
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL register field. */
#define ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL register field. */
#define ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL_MSB        19
/* The width in bits of the ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL register field. */
#define ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL_WIDTH      20
/* The mask used to set the ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL register field value. */
#define ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL_SET_MSK    0x000fffff
/* The mask used to clear the ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL register field value. */
#define ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL_CLR_MSK    0xfff00000
/* The reset value of the ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL register field is UNKNOWN. */
#define ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL_RESET      0x0
/* Extracts the ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL field value from a register. */
#define ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL_GET(value) (((value) & 0x000fffff) >> 0)
/* Produces a ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL register field value suitable for setting the register. */
#define ALT_SDR_CTL_QOSHIGHPRI_HIGHPRIORITYVAL_SET(value) (((value) << 0) & 0x000fffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_QOSHIGHPRI.
 */
struct ALT_SDR_CTL_QOSHIGHPRI_s
{
    uint32_t  highpriorityval : 20;  /* High Priority QoS Value */
    uint32_t                  : 12;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_QOSHIGHPRI. */
typedef volatile struct ALT_SDR_CTL_QOSHIGHPRI_s  ALT_SDR_CTL_QOSHIGHPRI_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_QOSHIGHPRI register from the beginning of the component. */
#define ALT_SDR_CTL_QOSHIGHPRI_OFST        0xa4

/*
 * Register : qospriorityen Register - qospriorityen
 * 
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description        
 * :--------|:-------|:--------|:--------------------
 *  [9:0]   | RW     | Unknown | Per-Port QoS Enable
 *  [31:10] | ???    | 0x0     | *UNDEFINED*        
 * 
 */
/*
 * Field : Per-Port QoS Enable - priorityen
 * 
 * This 10 bit field is set to a one to enable QOS usage for a port.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN register field. */
#define ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN register field. */
#define ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN_MSB        9
/* The width in bits of the ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN register field. */
#define ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN_WIDTH      10
/* The mask used to set the ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN register field value. */
#define ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN_SET_MSK    0x000003ff
/* The mask used to clear the ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN register field value. */
#define ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN_CLR_MSK    0xfffffc00
/* The reset value of the ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN register field is UNKNOWN. */
#define ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN_RESET      0x0
/* Extracts the ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN field value from a register. */
#define ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN_GET(value) (((value) & 0x000003ff) >> 0)
/* Produces a ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN register field value suitable for setting the register. */
#define ALT_SDR_CTL_QOSPRIORITYEN_PRIORITYEN_SET(value) (((value) << 0) & 0x000003ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_QOSPRIORITYEN.
 */
struct ALT_SDR_CTL_QOSPRIORITYEN_s
{
    uint32_t  priorityen : 10;  /* Per-Port QoS Enable */
    uint32_t             : 22;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_QOSPRIORITYEN. */
typedef volatile struct ALT_SDR_CTL_QOSPRIORITYEN_s  ALT_SDR_CTL_QOSPRIORITYEN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_QOSPRIORITYEN register from the beginning of the component. */
#define ALT_SDR_CTL_QOSPRIORITYEN_OFST        0xa8

/*
 * Register : Scheduler priority Register - mppriority
 * 
 * This register is used to configure the DRAM burst operation scheduling.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description         
 * :--------|:-------|:--------|:---------------------
 *  [29:0]  | RW     | Unknown | Port User Priorities
 *  [31:30] | ???    | 0x0     | *UNDEFINED*         
 * 
 */
/*
 * Field : Port User Priorities - userpriority
 * 
 * Set absolute user priority of the port.  Each port is represented by a 3 bit
 * value, 000=lowest priority, 111=highest priority.  Port 0 is bits 2:0.  Port
 * number offset corresponds to the control port assignment.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_MPPRIORITY_USERPRIORITY register field. */
#define ALT_SDR_CTL_MPPRIORITY_USERPRIORITY_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_MPPRIORITY_USERPRIORITY register field. */
#define ALT_SDR_CTL_MPPRIORITY_USERPRIORITY_MSB        29
/* The width in bits of the ALT_SDR_CTL_MPPRIORITY_USERPRIORITY register field. */
#define ALT_SDR_CTL_MPPRIORITY_USERPRIORITY_WIDTH      30
/* The mask used to set the ALT_SDR_CTL_MPPRIORITY_USERPRIORITY register field value. */
#define ALT_SDR_CTL_MPPRIORITY_USERPRIORITY_SET_MSK    0x3fffffff
/* The mask used to clear the ALT_SDR_CTL_MPPRIORITY_USERPRIORITY register field value. */
#define ALT_SDR_CTL_MPPRIORITY_USERPRIORITY_CLR_MSK    0xc0000000
/* The reset value of the ALT_SDR_CTL_MPPRIORITY_USERPRIORITY register field is UNKNOWN. */
#define ALT_SDR_CTL_MPPRIORITY_USERPRIORITY_RESET      0x0
/* Extracts the ALT_SDR_CTL_MPPRIORITY_USERPRIORITY field value from a register. */
#define ALT_SDR_CTL_MPPRIORITY_USERPRIORITY_GET(value) (((value) & 0x3fffffff) >> 0)
/* Produces a ALT_SDR_CTL_MPPRIORITY_USERPRIORITY register field value suitable for setting the register. */
#define ALT_SDR_CTL_MPPRIORITY_USERPRIORITY_SET(value) (((value) << 0) & 0x3fffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_MPPRIORITY.
 */
struct ALT_SDR_CTL_MPPRIORITY_s
{
    uint32_t  userpriority : 30;  /* Port User Priorities */
    uint32_t               :  2;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_MPPRIORITY. */
typedef volatile struct ALT_SDR_CTL_MPPRIORITY_s  ALT_SDR_CTL_MPPRIORITY_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_MPPRIORITY register from the beginning of the component. */
#define ALT_SDR_CTL_MPPRIORITY_OFST        0xac

/*
 * Register : Controller Command Pool Priority Remap Register - remappriority
 * 
 * This register controls the priority for transactions in the controller command
 * pool.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description   
 * :-------|:-------|:--------|:---------------
 *  [7:0]  | RW     | Unknown | Priority Remap
 *  [31:8] | ???    | 0x0     | *UNDEFINED*   
 * 
 */
/*
 * Field : Priority Remap - priorityremap
 * 
 * Set bit N of this register to the value to a one to enable the controller
 * command pool priority bit of a transaction from MPFE priority N
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP register field. */
#define ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP register field. */
#define ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP_MSB        7
/* The width in bits of the ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP register field. */
#define ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP_WIDTH      8
/* The mask used to set the ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP register field value. */
#define ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP_SET_MSK    0x000000ff
/* The mask used to clear the ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP register field value. */
#define ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP_CLR_MSK    0xffffff00
/* The reset value of the ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP register field is UNKNOWN. */
#define ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP_RESET      0x0
/* Extracts the ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP field value from a register. */
#define ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP register field value suitable for setting the register. */
#define ALT_SDR_CTL_REMAPPRIORITY_PRIORITYREMAP_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_REMAPPRIORITY.
 */
struct ALT_SDR_CTL_REMAPPRIORITY_s
{
    uint32_t  priorityremap :  8;  /* Priority Remap */
    uint32_t                : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_REMAPPRIORITY. */
typedef volatile struct ALT_SDR_CTL_REMAPPRIORITY_s  ALT_SDR_CTL_REMAPPRIORITY_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_REMAPPRIORITY register from the beginning of the component. */
#define ALT_SDR_CTL_REMAPPRIORITY_OFST        0xe0

/*
 * Register Group : Port Sum of Weight Register - ALT_SDR_CTL_MPWT
 * Port Sum of Weight Register
 * 
 * This register is used to configure the DRAM burst operation scheduling.
 * 
 */
/*
 * Register : Port Sum of Weight Register[1/4] - mpweight_0_4
 * 
 * This register is used to configure the DRAM burst operation scheduling.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description              
 * :-------|:-------|:--------|:--------------------------
 *  [31:0] | RW     | Unknown | Port Static Weights[31:0]
 * 
 */
/*
 * Field : Port Static Weights[31:0] - staticweight_31_0
 * 
 * Set static weight of the port.  Each port is programmed with a 5 bit value.
 * Port 0 is bits 4:0, port 1 is bits 9:5, up to port 9 being bits 49:45
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0_MSB        31
/* The width in bits of the ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0_WIDTH      32
/* The mask used to set the ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0 register field value. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0 register field value. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0_CLR_MSK    0x00000000
/* The reset value of the ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0 register field is UNKNOWN. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0_RESET      0x0
/* Extracts the ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0 field value from a register. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0 register field value suitable for setting the register. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_STATICWEIGHT_31_0_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_MPWT_MPWEIGHT_0_4.
 */
struct ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_s
{
    uint32_t  staticweight_31_0 : 32;  /* Port Static Weights[31:0] */
};

/* The typedef declaration for register ALT_SDR_CTL_MPWT_MPWEIGHT_0_4. */
typedef volatile struct ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_s  ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_MPWT_MPWEIGHT_0_4 register from the beginning of the component. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_OFST        0x0
/* The address of the ALT_SDR_CTL_MPWT_MPWEIGHT_0_4 register. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_OFST))

/*
 * Register : Port Sum of Weight Register[2/4] - mpweight_1_4
 * 
 * This register is used to configure the DRAM burst operation scheduling.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description               
 * :--------|:-------|:--------|:---------------------------
 *  [17:0]  | RW     | Unknown | Port Static Weights[49:32]
 *  [31:18] | RW     | Unknown | Port Sum of Weights[13:0] 
 * 
 */
/*
 * Field : Port Static Weights[49:32] - staticweight_49_32
 * 
 * Set static weight of the port.  Each port is programmed with a 5 bit value.
 * Port 0 is bits 4:0, port 1 is bits 9:5, up to port 9 being bits 49:45
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32_MSB        17
/* The width in bits of the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32_WIDTH      18
/* The mask used to set the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32 register field value. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32_SET_MSK    0x0003ffff
/* The mask used to clear the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32 register field value. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32_CLR_MSK    0xfffc0000
/* The reset value of the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32 register field is UNKNOWN. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32_RESET      0x0
/* Extracts the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32 field value from a register. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32_GET(value) (((value) & 0x0003ffff) >> 0)
/* Produces a ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32 register field value suitable for setting the register. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_STATICWEIGHT_49_32_SET(value) (((value) << 0) & 0x0003ffff)

/*
 * Field : Port Sum of Weights[13:0] - sumofweights_13_0
 * 
 * Set the sum of static weights for particular user priority.  This register is
 * used as part of the deficit round robin implementation.  It should be set to the
 * sum of the weights for the ports
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0_LSB        18
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0_MSB        31
/* The width in bits of the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0_WIDTH      14
/* The mask used to set the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0 register field value. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0_SET_MSK    0xfffc0000
/* The mask used to clear the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0 register field value. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0_CLR_MSK    0x0003ffff
/* The reset value of the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0 register field is UNKNOWN. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0_RESET      0x0
/* Extracts the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0 field value from a register. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0_GET(value) (((value) & 0xfffc0000) >> 18)
/* Produces a ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0 register field value suitable for setting the register. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_SUMOFWEIGHTS_13_0_SET(value) (((value) << 18) & 0xfffc0000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_MPWT_MPWEIGHT_1_4.
 */
struct ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_s
{
    uint32_t  staticweight_49_32 : 18;  /* Port Static Weights[49:32] */
    uint32_t  sumofweights_13_0  : 14;  /* Port Sum of Weights[13:0] */
};

/* The typedef declaration for register ALT_SDR_CTL_MPWT_MPWEIGHT_1_4. */
typedef volatile struct ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_s  ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4 register from the beginning of the component. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_OFST        0x4
/* The address of the ALT_SDR_CTL_MPWT_MPWEIGHT_1_4 register. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_OFST))

/*
 * Register : Port Sum of Weight Register[3/4] - mpweight_2_4
 * 
 * This register is used to configure the DRAM burst operation scheduling.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description               
 * :-------|:-------|:--------|:---------------------------
 *  [31:0] | RW     | Unknown | Port Sum of Weights[45:14]
 * 
 */
/*
 * Field : Port Sum of Weights[45:14] - sumofweights_45_14
 * 
 * Set the sum of static weights for particular user priority.  This register is
 * used as part of the deficit round robin implementation.  It should be set to the
 * sum of the weights for the ports
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14_MSB        31
/* The width in bits of the ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14_WIDTH      32
/* The mask used to set the ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14 register field value. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14_SET_MSK    0xffffffff
/* The mask used to clear the ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14 register field value. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14_CLR_MSK    0x00000000
/* The reset value of the ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14 register field is UNKNOWN. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14_RESET      0x0
/* Extracts the ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14 field value from a register. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14 register field value suitable for setting the register. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_SUMOFWEIGHTS_45_14_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_MPWT_MPWEIGHT_2_4.
 */
struct ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_s
{
    uint32_t  sumofweights_45_14 : 32;  /* Port Sum of Weights[45:14] */
};

/* The typedef declaration for register ALT_SDR_CTL_MPWT_MPWEIGHT_2_4. */
typedef volatile struct ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_s  ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_MPWT_MPWEIGHT_2_4 register from the beginning of the component. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_OFST        0x8
/* The address of the ALT_SDR_CTL_MPWT_MPWEIGHT_2_4 register. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_OFST))

/*
 * Register : Port Sum of Weight Register[4/4] - mpweight_3_4
 * 
 * This register is used to configure the DRAM burst operation scheduling.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description               
 * :--------|:-------|:--------|:---------------------------
 *  [17:0]  | RW     | Unknown | Port Sum of Weights[63:46]
 *  [31:18] | ???    | 0x0     | *UNDEFINED*               
 * 
 */
/*
 * Field : Port Sum of Weights[63:46] - sumofweights_63_46
 * 
 * Set the sum of static weights for particular user priority.  This register is
 * used as part of the deficit round robin implementation.  It should be set to the
 * sum of the weights for the ports
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46_MSB        17
/* The width in bits of the ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46 register field. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46_WIDTH      18
/* The mask used to set the ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46 register field value. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46_SET_MSK    0x0003ffff
/* The mask used to clear the ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46 register field value. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46_CLR_MSK    0xfffc0000
/* The reset value of the ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46 register field is UNKNOWN. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46_RESET      0x0
/* Extracts the ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46 field value from a register. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46_GET(value) (((value) & 0x0003ffff) >> 0)
/* Produces a ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46 register field value suitable for setting the register. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_SUMOFWEIGHTS_63_46_SET(value) (((value) << 0) & 0x0003ffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_SDR_CTL_MPWT_MPWEIGHT_3_4.
 */
struct ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_s
{
    uint32_t  sumofweights_63_46 : 18;  /* Port Sum of Weights[63:46] */
    uint32_t                     : 14;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_SDR_CTL_MPWT_MPWEIGHT_3_4. */
typedef volatile struct ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_s  ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_SDR_CTL_MPWT_MPWEIGHT_3_4 register from the beginning of the component. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_OFST        0xc
/* The address of the ALT_SDR_CTL_MPWT_MPWEIGHT_3_4 register. */
#define ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_SDR_CTL_MPWT.
 */
struct ALT_SDR_CTL_MPWT_s
{
    volatile ALT_SDR_CTL_MPWT_MPWEIGHT_0_4_t  mpweight_0_4;  /* ALT_SDR_CTL_MPWT_MPWEIGHT_0_4 */
    volatile ALT_SDR_CTL_MPWT_MPWEIGHT_1_4_t  mpweight_1_4;  /* ALT_SDR_CTL_MPWT_MPWEIGHT_1_4 */
    volatile ALT_SDR_CTL_MPWT_MPWEIGHT_2_4_t  mpweight_2_4;  /* ALT_SDR_CTL_MPWT_MPWEIGHT_2_4 */
    volatile ALT_SDR_CTL_MPWT_MPWEIGHT_3_4_t  mpweight_3_4;  /* ALT_SDR_CTL_MPWT_MPWEIGHT_3_4 */
};

/* The typedef declaration for register group ALT_SDR_CTL_MPWT. */
typedef volatile struct ALT_SDR_CTL_MPWT_s  ALT_SDR_CTL_MPWT_t;
/* The struct declaration for the raw register contents of register group ALT_SDR_CTL_MPWT. */
struct ALT_SDR_CTL_MPWT_raw_s
{
    volatile uint32_t  mpweight_0_4;  /* ALT_SDR_CTL_MPWT_MPWEIGHT_0_4 */
    volatile uint32_t  mpweight_1_4;  /* ALT_SDR_CTL_MPWT_MPWEIGHT_1_4 */
    volatile uint32_t  mpweight_2_4;  /* ALT_SDR_CTL_MPWT_MPWEIGHT_2_4 */
    volatile uint32_t  mpweight_3_4;  /* ALT_SDR_CTL_MPWT_MPWEIGHT_3_4 */
};

/* The typedef declaration for the raw register contents of register group ALT_SDR_CTL_MPWT. */
typedef volatile struct ALT_SDR_CTL_MPWT_raw_s  ALT_SDR_CTL_MPWT_raw_t;
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
 * The struct declaration for register group ALT_SDR_CTL.
 */
struct ALT_SDR_CTL_s
{
    volatile ALT_SDR_CTL_CTLCFG_t           ctrlcfg;                /* ALT_SDR_CTL_CTLCFG */
    volatile ALT_SDR_CTL_DRAMTIMING1_t      dramtiming1;            /* ALT_SDR_CTL_DRAMTIMING1 */
    volatile ALT_SDR_CTL_DRAMTIMING2_t      dramtiming2;            /* ALT_SDR_CTL_DRAMTIMING2 */
    volatile ALT_SDR_CTL_DRAMTIMING3_t      dramtiming3;            /* ALT_SDR_CTL_DRAMTIMING3 */
    volatile ALT_SDR_CTL_DRAMTIMING4_t      dramtiming4;            /* ALT_SDR_CTL_DRAMTIMING4 */
    volatile ALT_SDR_CTL_LOWPWRTIMING_t     lowpwrtiming;           /* ALT_SDR_CTL_LOWPWRTIMING */
    volatile ALT_SDR_CTL_DRAMODT_t          dramodt;                /* ALT_SDR_CTL_DRAMODT */
    volatile uint32_t                       _pad_0x1c_0x2b[4];      /* *UNDEFINED* */
    volatile ALT_SDR_CTL_DRAMADDRW_t        dramaddrw;              /* ALT_SDR_CTL_DRAMADDRW */
    volatile ALT_SDR_CTL_DRAMIFWIDTH_t      dramifwidth;            /* ALT_SDR_CTL_DRAMIFWIDTH */
    volatile ALT_SDR_CTL_DRAMDEVWIDTH_t     dramdevwidth;           /* ALT_SDR_CTL_DRAMDEVWIDTH */
    volatile ALT_SDR_CTL_DRAMSTS_t          dramsts;                /* ALT_SDR_CTL_DRAMSTS */
    volatile ALT_SDR_CTL_DRAMINTR_t         dramintr;               /* ALT_SDR_CTL_DRAMINTR */
    volatile ALT_SDR_CTL_SBECOUNT_t         sbecount;               /* ALT_SDR_CTL_SBECOUNT */
    volatile ALT_SDR_CTL_DBECOUNT_t         dbecount;               /* ALT_SDR_CTL_DBECOUNT */
    volatile ALT_SDR_CTL_ERRADDR_t          erraddr;                /* ALT_SDR_CTL_ERRADDR */
    volatile ALT_SDR_CTL_DROPCOUNT_t        dropcount;              /* ALT_SDR_CTL_DROPCOUNT */
    volatile ALT_SDR_CTL_DROPADDR_t         dropaddr;               /* ALT_SDR_CTL_DROPADDR */
    volatile ALT_SDR_CTL_LOWPWREQ_t         lowpwreq;               /* ALT_SDR_CTL_LOWPWREQ */
    volatile ALT_SDR_CTL_LOWPWRACK_t        lowpwrack;              /* ALT_SDR_CTL_LOWPWRACK */
    volatile ALT_SDR_CTL_STATICCFG_t        staticcfg;              /* ALT_SDR_CTL_STATICCFG */
    volatile ALT_SDR_CTL_CTLWIDTH_t         ctrlwidth;              /* ALT_SDR_CTL_CTLWIDTH */
    volatile uint32_t                       _pad_0x64_0x7b[6];      /* *UNDEFINED* */
    volatile ALT_SDR_CTL_PORTCFG_t          portcfg;                /* ALT_SDR_CTL_PORTCFG */
    volatile ALT_SDR_CTL_FPGAPORTRST_t      fpgaportrst;            /* ALT_SDR_CTL_FPGAPORTRST */
    volatile uint32_t                       _pad_0x84_0x8b[2];      /* *UNDEFINED* */
    volatile ALT_SDR_CTL_PROTPORTDEFAULT_t  protportdefault;        /* ALT_SDR_CTL_PROTPORTDEFAULT */
    volatile ALT_SDR_CTL_PROTRULEADDR_t     protruleaddr;           /* ALT_SDR_CTL_PROTRULEADDR */
    volatile ALT_SDR_CTL_PROTRULEID_t       protruleid;             /* ALT_SDR_CTL_PROTRULEID */
    volatile ALT_SDR_CTL_PROTRULEDATA_t     protruledata;           /* ALT_SDR_CTL_PROTRULEDATA */
    volatile ALT_SDR_CTL_PROTRULERDWR_t     protrulerdwr;           /* ALT_SDR_CTL_PROTRULERDWR */
    volatile ALT_SDR_CTL_QOSLOWPRI_t        qoslowpri;              /* ALT_SDR_CTL_QOSLOWPRI */
    volatile ALT_SDR_CTL_QOSHIGHPRI_t       qoshighpri;             /* ALT_SDR_CTL_QOSHIGHPRI */
    volatile ALT_SDR_CTL_QOSPRIORITYEN_t    qospriorityen;          /* ALT_SDR_CTL_QOSPRIORITYEN */
    volatile ALT_SDR_CTL_MPPRIORITY_t       mppriority;             /* ALT_SDR_CTL_MPPRIORITY */
    volatile ALT_SDR_CTL_MPWT_t             ctrlgrp_mpweight;       /* ALT_SDR_CTL_MPWT */
    volatile uint32_t                       _pad_0xc0_0xdf[8];      /* *UNDEFINED* */
    volatile ALT_SDR_CTL_REMAPPRIORITY_t    remappriority;          /* ALT_SDR_CTL_REMAPPRIORITY */
    volatile uint32_t                       _pad_0xe4_0x1000[967];  /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_SDR_CTL. */
typedef volatile struct ALT_SDR_CTL_s  ALT_SDR_CTL_t;
/* The struct declaration for the raw register contents of register group ALT_SDR_CTL. */
struct ALT_SDR_CTL_raw_s
{
    volatile uint32_t                ctrlcfg;                /* ALT_SDR_CTL_CTLCFG */
    volatile uint32_t                dramtiming1;            /* ALT_SDR_CTL_DRAMTIMING1 */
    volatile uint32_t                dramtiming2;            /* ALT_SDR_CTL_DRAMTIMING2 */
    volatile uint32_t                dramtiming3;            /* ALT_SDR_CTL_DRAMTIMING3 */
    volatile uint32_t                dramtiming4;            /* ALT_SDR_CTL_DRAMTIMING4 */
    volatile uint32_t                lowpwrtiming;           /* ALT_SDR_CTL_LOWPWRTIMING */
    volatile uint32_t                dramodt;                /* ALT_SDR_CTL_DRAMODT */
    volatile uint32_t                _pad_0x1c_0x2b[4];      /* *UNDEFINED* */
    volatile uint32_t                dramaddrw;              /* ALT_SDR_CTL_DRAMADDRW */
    volatile uint32_t                dramifwidth;            /* ALT_SDR_CTL_DRAMIFWIDTH */
    volatile uint32_t                dramdevwidth;           /* ALT_SDR_CTL_DRAMDEVWIDTH */
    volatile uint32_t                dramsts;                /* ALT_SDR_CTL_DRAMSTS */
    volatile uint32_t                dramintr;               /* ALT_SDR_CTL_DRAMINTR */
    volatile uint32_t                sbecount;               /* ALT_SDR_CTL_SBECOUNT */
    volatile uint32_t                dbecount;               /* ALT_SDR_CTL_DBECOUNT */
    volatile uint32_t                erraddr;                /* ALT_SDR_CTL_ERRADDR */
    volatile uint32_t                dropcount;              /* ALT_SDR_CTL_DROPCOUNT */
    volatile uint32_t                dropaddr;               /* ALT_SDR_CTL_DROPADDR */
    volatile uint32_t                lowpwreq;               /* ALT_SDR_CTL_LOWPWREQ */
    volatile uint32_t                lowpwrack;              /* ALT_SDR_CTL_LOWPWRACK */
    volatile uint32_t                staticcfg;              /* ALT_SDR_CTL_STATICCFG */
    volatile uint32_t                ctrlwidth;              /* ALT_SDR_CTL_CTLWIDTH */
    volatile uint32_t                _pad_0x64_0x7b[6];      /* *UNDEFINED* */
    volatile uint32_t                portcfg;                /* ALT_SDR_CTL_PORTCFG */
    volatile uint32_t                fpgaportrst;            /* ALT_SDR_CTL_FPGAPORTRST */
    volatile uint32_t                _pad_0x84_0x8b[2];      /* *UNDEFINED* */
    volatile uint32_t                protportdefault;        /* ALT_SDR_CTL_PROTPORTDEFAULT */
    volatile uint32_t                protruleaddr;           /* ALT_SDR_CTL_PROTRULEADDR */
    volatile uint32_t                protruleid;             /* ALT_SDR_CTL_PROTRULEID */
    volatile uint32_t                protruledata;           /* ALT_SDR_CTL_PROTRULEDATA */
    volatile uint32_t                protrulerdwr;           /* ALT_SDR_CTL_PROTRULERDWR */
    volatile uint32_t                qoslowpri;              /* ALT_SDR_CTL_QOSLOWPRI */
    volatile uint32_t                qoshighpri;             /* ALT_SDR_CTL_QOSHIGHPRI */
    volatile uint32_t                qospriorityen;          /* ALT_SDR_CTL_QOSPRIORITYEN */
    volatile uint32_t                mppriority;             /* ALT_SDR_CTL_MPPRIORITY */
    volatile ALT_SDR_CTL_MPWT_raw_t  ctrlgrp_mpweight;       /* ALT_SDR_CTL_MPWT */
    volatile uint32_t                _pad_0xc0_0xdf[8];      /* *UNDEFINED* */
    volatile uint32_t                remappriority;          /* ALT_SDR_CTL_REMAPPRIORITY */
    volatile uint32_t                _pad_0xe4_0x1000[967];  /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_SDR_CTL. */
typedef volatile struct ALT_SDR_CTL_raw_s  ALT_SDR_CTL_raw_t;
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
 * The struct declaration for register group ALT_SDR.
 */
struct ALT_SDR_s
{
    volatile uint32_t       _pad_0x0_0x4fff[5120];       /* *UNDEFINED* */
    volatile ALT_SDR_CTL_t  ctrlgrp;                     /* ALT_SDR_CTL */
    volatile uint32_t       _pad_0x6000_0x20000[26624];  /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_SDR. */
typedef volatile struct ALT_SDR_s  ALT_SDR_t;
/* The struct declaration for the raw register contents of register group ALT_SDR. */
struct ALT_SDR_raw_s
{
    volatile uint32_t           _pad_0x0_0x4fff[5120];       /* *UNDEFINED* */
    volatile ALT_SDR_CTL_raw_t  ctrlgrp;                     /* ALT_SDR_CTL */
    volatile uint32_t           _pad_0x6000_0x20000[26624];  /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_SDR. */
typedef volatile struct ALT_SDR_raw_s  ALT_SDR_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_SDR_H__ */

