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

/* Altera - ALT_LWH2F */

#ifndef __ALTERA_ALT_LWH2F_H__
#define __ALTERA_ALT_LWH2F_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : LWHPS2FPGA AXI Bridge Module - ALT_LWH2F
 * LWHPS2FPGA AXI Bridge Module
 * 
 * Registers in the LWHPS2FPGA AXI Bridge Module.
 * 
 */
/*
 * Register Group : ID Register Group - ALT_LWH2F_ID
 * ID Register Group
 * 
 * Contains registers that identify the ARM NIC-301 IP Core.
 * 
 */
/*
 * Register : Peripheral ID4 Register - periph_id_4
 * 
 * JEP106 continuation code
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description   
 * :-------|:-------|:------|:---------------
 *  [7:0]  | R      | 0x4   | Peripheral ID4
 *  [31:8] | ???    | 0x0   | *UNDEFINED*   
 * 
 */
/*
 * Field : Peripheral ID4 - periph_id_4
 * 
 * JEP106 continuation code
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4_MSB        7
/* The width in bits of the ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4_WIDTH      8
/* The mask used to set the ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4 register field value. */
#define ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4_SET_MSK    0x000000ff
/* The mask used to clear the ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4 register field value. */
#define ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4_CLR_MSK    0xffffff00
/* The reset value of the ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4_RESET      0x4
/* Extracts the ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4 field value from a register. */
#define ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4 register field value suitable for setting the register. */
#define ALT_LWH2F_ID_PERIPH_ID_4_PERIPH_ID_4_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_LWH2F_ID_PERIPH_ID_4.
 */
struct ALT_LWH2F_ID_PERIPH_ID_4_s
{
    const uint32_t  periph_id_4 :  8;  /* Peripheral ID4 */
    uint32_t                    : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_LWH2F_ID_PERIPH_ID_4. */
typedef volatile struct ALT_LWH2F_ID_PERIPH_ID_4_s  ALT_LWH2F_ID_PERIPH_ID_4_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_LWH2F_ID_PERIPH_ID_4 register from the beginning of the component. */
#define ALT_LWH2F_ID_PERIPH_ID_4_OFST        0xfd0

/*
 * Register : Peripheral ID0 Register - periph_id_0
 * 
 * Peripheral ID0
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description      
 * :-------|:-------|:------|:------------------
 *  [7:0]  | R      | 0x1   | Part Number [7:0]
 *  [31:8] | ???    | 0x0   | *UNDEFINED*      
 * 
 */
/*
 * Field : Part Number [7:0] - pn7to0
 * 
 * Part Number [7:0]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0_MSB        7
/* The width in bits of the ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0_WIDTH      8
/* The mask used to set the ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0 register field value. */
#define ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0_SET_MSK    0x000000ff
/* The mask used to clear the ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0 register field value. */
#define ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0_CLR_MSK    0xffffff00
/* The reset value of the ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0_RESET      0x1
/* Extracts the ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0 field value from a register. */
#define ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0 register field value suitable for setting the register. */
#define ALT_LWH2F_ID_PERIPH_ID_0_PN7TO0_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_LWH2F_ID_PERIPH_ID_0.
 */
struct ALT_LWH2F_ID_PERIPH_ID_0_s
{
    const uint32_t  pn7to0 :  8;  /* Part Number [7:0] */
    uint32_t               : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_LWH2F_ID_PERIPH_ID_0. */
typedef volatile struct ALT_LWH2F_ID_PERIPH_ID_0_s  ALT_LWH2F_ID_PERIPH_ID_0_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_LWH2F_ID_PERIPH_ID_0 register from the beginning of the component. */
#define ALT_LWH2F_ID_PERIPH_ID_0_OFST        0xfe0

/*
 * Register : Peripheral ID1 Register - periph_id_1
 * 
 * Peripheral ID1
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                    
 * :-------|:-------|:------|:--------------------------------
 *  [7:0]  | R      | 0xb3  | JEP106[3:0], Part Number [11:8]
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                    
 * 
 */
/*
 * Field : JEP106[3:0], Part Number [11:8] - jep3to0_pn11to8
 * 
 * JEP106[3:0], Part Number [11:8]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_MSB        7
/* The width in bits of the ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_WIDTH      8
/* The mask used to set the ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 register field value. */
#define ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_SET_MSK    0x000000ff
/* The mask used to clear the ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 register field value. */
#define ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_CLR_MSK    0xffffff00
/* The reset value of the ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_RESET      0xb3
/* Extracts the ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 field value from a register. */
#define ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 register field value suitable for setting the register. */
#define ALT_LWH2F_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_LWH2F_ID_PERIPH_ID_1.
 */
struct ALT_LWH2F_ID_PERIPH_ID_1_s
{
    const uint32_t  jep3to0_pn11to8 :  8;  /* JEP106[3:0], Part Number [11:8] */
    uint32_t                        : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_LWH2F_ID_PERIPH_ID_1. */
typedef volatile struct ALT_LWH2F_ID_PERIPH_ID_1_s  ALT_LWH2F_ID_PERIPH_ID_1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_LWH2F_ID_PERIPH_ID_1 register from the beginning of the component. */
#define ALT_LWH2F_ID_PERIPH_ID_1_OFST        0xfe4

/*
 * Register : Peripheral ID2 Register - periph_id_2
 * 
 * Peripheral ID2
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                            
 * :-------|:-------|:------|:----------------------------------------
 *  [7:0]  | R      | 0x6b  | Revision, JEP106 code flag, JEP106[6:4]
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                            
 * 
 */
/*
 * Field : Revision, JEP106 code flag, JEP106[6:4] - rev_jepcode_jep6to4
 * 
 * Revision, JEP106 code flag, JEP106[6:4]
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_MSB        7
/* The width in bits of the ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_WIDTH      8
/* The mask used to set the ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 register field value. */
#define ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_SET_MSK    0x000000ff
/* The mask used to clear the ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 register field value. */
#define ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_CLR_MSK    0xffffff00
/* The reset value of the ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 register field. */
#define ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_RESET      0x6b
/* Extracts the ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 field value from a register. */
#define ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 register field value suitable for setting the register. */
#define ALT_LWH2F_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_LWH2F_ID_PERIPH_ID_2.
 */
struct ALT_LWH2F_ID_PERIPH_ID_2_s
{
    const uint32_t  rev_jepcode_jep6to4 :  8;  /* Revision, JEP106 code flag, JEP106[6:4] */
    uint32_t                            : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_LWH2F_ID_PERIPH_ID_2. */
typedef volatile struct ALT_LWH2F_ID_PERIPH_ID_2_s  ALT_LWH2F_ID_PERIPH_ID_2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_LWH2F_ID_PERIPH_ID_2 register from the beginning of the component. */
#define ALT_LWH2F_ID_PERIPH_ID_2_OFST        0xfe8

/*
 * Register : Peripheral ID3 Register - periph_id_3
 * 
 * Peripheral ID3
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description          
 * :-------|:-------|:------|:----------------------
 *  [3:0]  | R      | 0x0   | Customer Model Number
 *  [7:4]  | R      | 0x0   | Revision             
 *  [31:8] | ???    | 0x0   | *UNDEFINED*          
 * 
 */
/*
 * Field : Customer Model Number - cust_mod_num
 * 
 * Customer Model Number
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM register field. */
#define ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM register field. */
#define ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM_MSB        3
/* The width in bits of the ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM register field. */
#define ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM_WIDTH      4
/* The mask used to set the ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM register field value. */
#define ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM_SET_MSK    0x0000000f
/* The mask used to clear the ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM register field value. */
#define ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM_CLR_MSK    0xfffffff0
/* The reset value of the ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM register field. */
#define ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM_RESET      0x0
/* Extracts the ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM field value from a register. */
#define ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM register field value suitable for setting the register. */
#define ALT_LWH2F_ID_PERIPH_ID_3_CUST_MOD_NUM_SET(value) (((value) << 0) & 0x0000000f)

/*
 * Field : Revision - rev_and
 * 
 * Revision
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_LWH2F_ID_PERIPH_ID_3_REV_AND register field. */
#define ALT_LWH2F_ID_PERIPH_ID_3_REV_AND_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_ID_PERIPH_ID_3_REV_AND register field. */
#define ALT_LWH2F_ID_PERIPH_ID_3_REV_AND_MSB        7
/* The width in bits of the ALT_LWH2F_ID_PERIPH_ID_3_REV_AND register field. */
#define ALT_LWH2F_ID_PERIPH_ID_3_REV_AND_WIDTH      4
/* The mask used to set the ALT_LWH2F_ID_PERIPH_ID_3_REV_AND register field value. */
#define ALT_LWH2F_ID_PERIPH_ID_3_REV_AND_SET_MSK    0x000000f0
/* The mask used to clear the ALT_LWH2F_ID_PERIPH_ID_3_REV_AND register field value. */
#define ALT_LWH2F_ID_PERIPH_ID_3_REV_AND_CLR_MSK    0xffffff0f
/* The reset value of the ALT_LWH2F_ID_PERIPH_ID_3_REV_AND register field. */
#define ALT_LWH2F_ID_PERIPH_ID_3_REV_AND_RESET      0x0
/* Extracts the ALT_LWH2F_ID_PERIPH_ID_3_REV_AND field value from a register. */
#define ALT_LWH2F_ID_PERIPH_ID_3_REV_AND_GET(value) (((value) & 0x000000f0) >> 4)
/* Produces a ALT_LWH2F_ID_PERIPH_ID_3_REV_AND register field value suitable for setting the register. */
#define ALT_LWH2F_ID_PERIPH_ID_3_REV_AND_SET(value) (((value) << 4) & 0x000000f0)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_LWH2F_ID_PERIPH_ID_3.
 */
struct ALT_LWH2F_ID_PERIPH_ID_3_s
{
    const uint32_t  cust_mod_num :  4;  /* Customer Model Number */
    const uint32_t  rev_and      :  4;  /* Revision */
    uint32_t                     : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_LWH2F_ID_PERIPH_ID_3. */
typedef volatile struct ALT_LWH2F_ID_PERIPH_ID_3_s  ALT_LWH2F_ID_PERIPH_ID_3_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_LWH2F_ID_PERIPH_ID_3 register from the beginning of the component. */
#define ALT_LWH2F_ID_PERIPH_ID_3_OFST        0xfec

/*
 * Register : Component ID0 Register - comp_id_0
 * 
 * Component ID0
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [7:0]  | R      | 0xd   | Preamble   
 *  [31:8] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Preamble - preamble
 * 
 * Preamble
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_LWH2F_ID_COMP_ID_0_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_0_PREAMBLE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_ID_COMP_ID_0_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_0_PREAMBLE_MSB        7
/* The width in bits of the ALT_LWH2F_ID_COMP_ID_0_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_0_PREAMBLE_WIDTH      8
/* The mask used to set the ALT_LWH2F_ID_COMP_ID_0_PREAMBLE register field value. */
#define ALT_LWH2F_ID_COMP_ID_0_PREAMBLE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_LWH2F_ID_COMP_ID_0_PREAMBLE register field value. */
#define ALT_LWH2F_ID_COMP_ID_0_PREAMBLE_CLR_MSK    0xffffff00
/* The reset value of the ALT_LWH2F_ID_COMP_ID_0_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_0_PREAMBLE_RESET      0xd
/* Extracts the ALT_LWH2F_ID_COMP_ID_0_PREAMBLE field value from a register. */
#define ALT_LWH2F_ID_COMP_ID_0_PREAMBLE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_LWH2F_ID_COMP_ID_0_PREAMBLE register field value suitable for setting the register. */
#define ALT_LWH2F_ID_COMP_ID_0_PREAMBLE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_LWH2F_ID_COMP_ID_0.
 */
struct ALT_LWH2F_ID_COMP_ID_0_s
{
    const uint32_t  preamble :  8;  /* Preamble */
    uint32_t                 : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_LWH2F_ID_COMP_ID_0. */
typedef volatile struct ALT_LWH2F_ID_COMP_ID_0_s  ALT_LWH2F_ID_COMP_ID_0_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_LWH2F_ID_COMP_ID_0 register from the beginning of the component. */
#define ALT_LWH2F_ID_COMP_ID_0_OFST        0xff0

/*
 * Register : Component ID1 Register - comp_id_1
 * 
 * Component ID1
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                         
 * :-------|:-------|:------|:-------------------------------------
 *  [7:0]  | R      | 0xf0  | Generic IP component class, Preamble
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                         
 * 
 */
/*
 * Field : Generic IP component class, Preamble - genipcompcls_preamble
 * 
 * Generic IP component class, Preamble
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_MSB        7
/* The width in bits of the ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_WIDTH      8
/* The mask used to set the ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE register field value. */
#define ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE register field value. */
#define ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_CLR_MSK    0xffffff00
/* The reset value of the ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_RESET      0xf0
/* Extracts the ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE field value from a register. */
#define ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE register field value suitable for setting the register. */
#define ALT_LWH2F_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_LWH2F_ID_COMP_ID_1.
 */
struct ALT_LWH2F_ID_COMP_ID_1_s
{
    const uint32_t  genipcompcls_preamble :  8;  /* Generic IP component class, Preamble */
    uint32_t                              : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_LWH2F_ID_COMP_ID_1. */
typedef volatile struct ALT_LWH2F_ID_COMP_ID_1_s  ALT_LWH2F_ID_COMP_ID_1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_LWH2F_ID_COMP_ID_1 register from the beginning of the component. */
#define ALT_LWH2F_ID_COMP_ID_1_OFST        0xff4

/*
 * Register : Component ID2 Register - comp_id_2
 * 
 * Component ID2
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [7:0]  | R      | 0x5   | Preamble   
 *  [31:8] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Preamble - preamble
 * 
 * Preamble
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_LWH2F_ID_COMP_ID_2_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_2_PREAMBLE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_ID_COMP_ID_2_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_2_PREAMBLE_MSB        7
/* The width in bits of the ALT_LWH2F_ID_COMP_ID_2_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_2_PREAMBLE_WIDTH      8
/* The mask used to set the ALT_LWH2F_ID_COMP_ID_2_PREAMBLE register field value. */
#define ALT_LWH2F_ID_COMP_ID_2_PREAMBLE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_LWH2F_ID_COMP_ID_2_PREAMBLE register field value. */
#define ALT_LWH2F_ID_COMP_ID_2_PREAMBLE_CLR_MSK    0xffffff00
/* The reset value of the ALT_LWH2F_ID_COMP_ID_2_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_2_PREAMBLE_RESET      0x5
/* Extracts the ALT_LWH2F_ID_COMP_ID_2_PREAMBLE field value from a register. */
#define ALT_LWH2F_ID_COMP_ID_2_PREAMBLE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_LWH2F_ID_COMP_ID_2_PREAMBLE register field value suitable for setting the register. */
#define ALT_LWH2F_ID_COMP_ID_2_PREAMBLE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_LWH2F_ID_COMP_ID_2.
 */
struct ALT_LWH2F_ID_COMP_ID_2_s
{
    const uint32_t  preamble :  8;  /* Preamble */
    uint32_t                 : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_LWH2F_ID_COMP_ID_2. */
typedef volatile struct ALT_LWH2F_ID_COMP_ID_2_s  ALT_LWH2F_ID_COMP_ID_2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_LWH2F_ID_COMP_ID_2 register from the beginning of the component. */
#define ALT_LWH2F_ID_COMP_ID_2_OFST        0xff8

/*
 * Register : Component ID3 Register - comp_id_3
 * 
 * Component ID3
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [7:0]  | R      | 0xb1  | Preamble   
 *  [31:8] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Preamble - preamble
 * 
 * Preamble
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_LWH2F_ID_COMP_ID_3_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_3_PREAMBLE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_ID_COMP_ID_3_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_3_PREAMBLE_MSB        7
/* The width in bits of the ALT_LWH2F_ID_COMP_ID_3_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_3_PREAMBLE_WIDTH      8
/* The mask used to set the ALT_LWH2F_ID_COMP_ID_3_PREAMBLE register field value. */
#define ALT_LWH2F_ID_COMP_ID_3_PREAMBLE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_LWH2F_ID_COMP_ID_3_PREAMBLE register field value. */
#define ALT_LWH2F_ID_COMP_ID_3_PREAMBLE_CLR_MSK    0xffffff00
/* The reset value of the ALT_LWH2F_ID_COMP_ID_3_PREAMBLE register field. */
#define ALT_LWH2F_ID_COMP_ID_3_PREAMBLE_RESET      0xb1
/* Extracts the ALT_LWH2F_ID_COMP_ID_3_PREAMBLE field value from a register. */
#define ALT_LWH2F_ID_COMP_ID_3_PREAMBLE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_LWH2F_ID_COMP_ID_3_PREAMBLE register field value suitable for setting the register. */
#define ALT_LWH2F_ID_COMP_ID_3_PREAMBLE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_LWH2F_ID_COMP_ID_3.
 */
struct ALT_LWH2F_ID_COMP_ID_3_s
{
    const uint32_t  preamble :  8;  /* Preamble */
    uint32_t                 : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_LWH2F_ID_COMP_ID_3. */
typedef volatile struct ALT_LWH2F_ID_COMP_ID_3_s  ALT_LWH2F_ID_COMP_ID_3_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_LWH2F_ID_COMP_ID_3 register from the beginning of the component. */
#define ALT_LWH2F_ID_COMP_ID_3_OFST        0xffc

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_LWH2F_ID.
 */
struct ALT_LWH2F_ID_s
{
    volatile uint32_t                    _pad_0x0_0xfcf[1012];  /* *UNDEFINED* */
    volatile ALT_LWH2F_ID_PERIPH_ID_4_t  periph_id_4;           /* ALT_LWH2F_ID_PERIPH_ID_4 */
    volatile uint32_t                    _pad_0xfd4_0xfdf[3];   /* *UNDEFINED* */
    volatile ALT_LWH2F_ID_PERIPH_ID_0_t  periph_id_0;           /* ALT_LWH2F_ID_PERIPH_ID_0 */
    volatile ALT_LWH2F_ID_PERIPH_ID_1_t  periph_id_1;           /* ALT_LWH2F_ID_PERIPH_ID_1 */
    volatile ALT_LWH2F_ID_PERIPH_ID_2_t  periph_id_2;           /* ALT_LWH2F_ID_PERIPH_ID_2 */
    volatile ALT_LWH2F_ID_PERIPH_ID_3_t  periph_id_3;           /* ALT_LWH2F_ID_PERIPH_ID_3 */
    volatile ALT_LWH2F_ID_COMP_ID_0_t    comp_id_0;             /* ALT_LWH2F_ID_COMP_ID_0 */
    volatile ALT_LWH2F_ID_COMP_ID_1_t    comp_id_1;             /* ALT_LWH2F_ID_COMP_ID_1 */
    volatile ALT_LWH2F_ID_COMP_ID_2_t    comp_id_2;             /* ALT_LWH2F_ID_COMP_ID_2 */
    volatile ALT_LWH2F_ID_COMP_ID_3_t    comp_id_3;             /* ALT_LWH2F_ID_COMP_ID_3 */
};

/* The typedef declaration for register group ALT_LWH2F_ID. */
typedef volatile struct ALT_LWH2F_ID_s  ALT_LWH2F_ID_t;
/* The struct declaration for the raw register contents of register group ALT_LWH2F_ID. */
struct ALT_LWH2F_ID_raw_s
{
    volatile uint32_t  _pad_0x0_0xfcf[1012];  /* *UNDEFINED* */
    volatile uint32_t  periph_id_4;           /* ALT_LWH2F_ID_PERIPH_ID_4 */
    volatile uint32_t  _pad_0xfd4_0xfdf[3];   /* *UNDEFINED* */
    volatile uint32_t  periph_id_0;           /* ALT_LWH2F_ID_PERIPH_ID_0 */
    volatile uint32_t  periph_id_1;           /* ALT_LWH2F_ID_PERIPH_ID_1 */
    volatile uint32_t  periph_id_2;           /* ALT_LWH2F_ID_PERIPH_ID_2 */
    volatile uint32_t  periph_id_3;           /* ALT_LWH2F_ID_PERIPH_ID_3 */
    volatile uint32_t  comp_id_0;             /* ALT_LWH2F_ID_COMP_ID_0 */
    volatile uint32_t  comp_id_1;             /* ALT_LWH2F_ID_COMP_ID_1 */
    volatile uint32_t  comp_id_2;             /* ALT_LWH2F_ID_COMP_ID_2 */
    volatile uint32_t  comp_id_3;             /* ALT_LWH2F_ID_COMP_ID_3 */
};

/* The typedef declaration for the raw register contents of register group ALT_LWH2F_ID. */
typedef volatile struct ALT_LWH2F_ID_raw_s  ALT_LWH2F_ID_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : Master Register Group - ALT_LWH2F_MST
 * Master Register Group
 * 
 * Registers associated with master interfaces.
 * 
 */
/*
 * Register Group : FPGA2HPS AXI Bridge Registers - ALT_LWH2F_MST_F2H
 * FPGA2HPS AXI Bridge Registers
 * 
 * Registers associated with the FPGA2HPS master interface.
 * 
 * This master interface provides access to the registers in the FPGA2HPS AXI
 * Bridge.
 * 
 */
/*
 * Register : Bus Matrix Issuing Functionality Modification Register - fn_mod_bm_iss
 * 
 * Sets the issuing capability of the preceding switch arbitration scheme to
 * multiple or single outstanding transactions.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description               
 * :-------|:-------|:------|:---------------------------
 *  [0]    | RW     | 0x0   | ALT_LWH2F_FN_MOD_BM_ISS_RD
 *  [1]    | RW     | 0x0   | ALT_LWH2F_FN_MOD_BM_ISS_WR
 *  [31:2] | ???    | 0x0   | *UNDEFINED*               
 * 
 */
/*
 * Field : rd
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                               
 * :------------------------------------|:------|:-------------------------------------------
 *  ALT_LWH2F_FN_MOD_BM_ISS_RD_E_MULT   | 0x0   | Multiple outstanding read transactions    
 *  ALT_LWH2F_FN_MOD_BM_ISS_RD_E_SINGLE | 0x1   | Only a single outstanding read transaction
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_LWH2F_FN_MOD_BM_ISS_RD
 * 
 * Multiple outstanding read transactions
 */
#define ALT_LWH2F_FN_MOD_BM_ISS_RD_E_MULT   0x0
/*
 * Enumerated value for register field ALT_LWH2F_FN_MOD_BM_ISS_RD
 * 
 * Only a single outstanding read transaction
 */
#define ALT_LWH2F_FN_MOD_BM_ISS_RD_E_SINGLE 0x1

/* The Least Significant Bit (LSB) position of the ALT_LWH2F_FN_MOD_BM_ISS_RD register field. */
#define ALT_LWH2F_FN_MOD_BM_ISS_RD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_FN_MOD_BM_ISS_RD register field. */
#define ALT_LWH2F_FN_MOD_BM_ISS_RD_MSB        0
/* The width in bits of the ALT_LWH2F_FN_MOD_BM_ISS_RD register field. */
#define ALT_LWH2F_FN_MOD_BM_ISS_RD_WIDTH      1
/* The mask used to set the ALT_LWH2F_FN_MOD_BM_ISS_RD register field value. */
#define ALT_LWH2F_FN_MOD_BM_ISS_RD_SET_MSK    0x00000001
/* The mask used to clear the ALT_LWH2F_FN_MOD_BM_ISS_RD register field value. */
#define ALT_LWH2F_FN_MOD_BM_ISS_RD_CLR_MSK    0xfffffffe
/* The reset value of the ALT_LWH2F_FN_MOD_BM_ISS_RD register field. */
#define ALT_LWH2F_FN_MOD_BM_ISS_RD_RESET      0x0
/* Extracts the ALT_LWH2F_FN_MOD_BM_ISS_RD field value from a register. */
#define ALT_LWH2F_FN_MOD_BM_ISS_RD_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_LWH2F_FN_MOD_BM_ISS_RD register field value suitable for setting the register. */
#define ALT_LWH2F_FN_MOD_BM_ISS_RD_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : wr
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                                
 * :------------------------------------|:------|:--------------------------------------------
 *  ALT_LWH2F_FN_MOD_BM_ISS_WR_E_MULT   | 0x0   | Multiple outstanding write transactions    
 *  ALT_LWH2F_FN_MOD_BM_ISS_WR_E_SINGLE | 0x1   | Only a single outstanding write transaction
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_LWH2F_FN_MOD_BM_ISS_WR
 * 
 * Multiple outstanding write transactions
 */
#define ALT_LWH2F_FN_MOD_BM_ISS_WR_E_MULT   0x0
/*
 * Enumerated value for register field ALT_LWH2F_FN_MOD_BM_ISS_WR
 * 
 * Only a single outstanding write transaction
 */
#define ALT_LWH2F_FN_MOD_BM_ISS_WR_E_SINGLE 0x1

/* The Least Significant Bit (LSB) position of the ALT_LWH2F_FN_MOD_BM_ISS_WR register field. */
#define ALT_LWH2F_FN_MOD_BM_ISS_WR_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_FN_MOD_BM_ISS_WR register field. */
#define ALT_LWH2F_FN_MOD_BM_ISS_WR_MSB        1
/* The width in bits of the ALT_LWH2F_FN_MOD_BM_ISS_WR register field. */
#define ALT_LWH2F_FN_MOD_BM_ISS_WR_WIDTH      1
/* The mask used to set the ALT_LWH2F_FN_MOD_BM_ISS_WR register field value. */
#define ALT_LWH2F_FN_MOD_BM_ISS_WR_SET_MSK    0x00000002
/* The mask used to clear the ALT_LWH2F_FN_MOD_BM_ISS_WR register field value. */
#define ALT_LWH2F_FN_MOD_BM_ISS_WR_CLR_MSK    0xfffffffd
/* The reset value of the ALT_LWH2F_FN_MOD_BM_ISS_WR register field. */
#define ALT_LWH2F_FN_MOD_BM_ISS_WR_RESET      0x0
/* Extracts the ALT_LWH2F_FN_MOD_BM_ISS_WR field value from a register. */
#define ALT_LWH2F_FN_MOD_BM_ISS_WR_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_LWH2F_FN_MOD_BM_ISS_WR register field value suitable for setting the register. */
#define ALT_LWH2F_FN_MOD_BM_ISS_WR_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_LWH2F_FN_MOD_BM_ISS.
 */
struct ALT_LWH2F_FN_MOD_BM_ISS_s
{
    uint32_t  rd :  1;  /* ALT_LWH2F_FN_MOD_BM_ISS_RD */
    uint32_t  wr :  1;  /* ALT_LWH2F_FN_MOD_BM_ISS_WR */
    uint32_t     : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_LWH2F_FN_MOD_BM_ISS. */
typedef volatile struct ALT_LWH2F_FN_MOD_BM_ISS_s  ALT_LWH2F_FN_MOD_BM_ISS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_LWH2F_FN_MOD_BM_ISS register from the beginning of the component. */
#define ALT_LWH2F_FN_MOD_BM_ISS_OFST        0x8
/* The address of the ALT_LWH2F_FN_MOD_BM_ISS register. */
#define ALT_LWH2F_FN_MOD_BM_ISS_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_LWH2F_FN_MOD_BM_ISS_OFST))

/*
 * Register : AHB Control Register - ahb_cntl
 * 
 * Sets the block issuing capability to one outstanding transaction.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [0]    | RW     | 0x0   | ALT_LWH2F_AHB_CNTL_DECERR_EN 
 *  [1]    | RW     | 0x0   | ALT_LWH2F_AHB_CNTL_FORCE_INCR
 *  [31:2] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : decerr_en
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                                     
 * :-----------------------------------|:------|:-------------------------------------------------
 *  ALT_LWH2F_AHB_CNTL_DECERR_EN_E_DIS | 0x0   | No DECERR response.                             
 *  ALT_LWH2F_AHB_CNTL_DECERR_EN_E_EN  | 0x1   | If the AHB protocol conversion function receives
 * :                                   |       | an unaligned address or a write data beat       
 * :                                   |       | without all the byte strobes set, creates a     
 * :                                   |       | DECERR response.                                
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_LWH2F_AHB_CNTL_DECERR_EN
 * 
 * No DECERR response.
 */
#define ALT_LWH2F_AHB_CNTL_DECERR_EN_E_DIS  0x0
/*
 * Enumerated value for register field ALT_LWH2F_AHB_CNTL_DECERR_EN
 * 
 * If the AHB protocol conversion function receives an unaligned address or a write
 * data beat without all the byte strobes set, creates a DECERR response.
 */
#define ALT_LWH2F_AHB_CNTL_DECERR_EN_E_EN   0x1

/* The Least Significant Bit (LSB) position of the ALT_LWH2F_AHB_CNTL_DECERR_EN register field. */
#define ALT_LWH2F_AHB_CNTL_DECERR_EN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_AHB_CNTL_DECERR_EN register field. */
#define ALT_LWH2F_AHB_CNTL_DECERR_EN_MSB        0
/* The width in bits of the ALT_LWH2F_AHB_CNTL_DECERR_EN register field. */
#define ALT_LWH2F_AHB_CNTL_DECERR_EN_WIDTH      1
/* The mask used to set the ALT_LWH2F_AHB_CNTL_DECERR_EN register field value. */
#define ALT_LWH2F_AHB_CNTL_DECERR_EN_SET_MSK    0x00000001
/* The mask used to clear the ALT_LWH2F_AHB_CNTL_DECERR_EN register field value. */
#define ALT_LWH2F_AHB_CNTL_DECERR_EN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_LWH2F_AHB_CNTL_DECERR_EN register field. */
#define ALT_LWH2F_AHB_CNTL_DECERR_EN_RESET      0x0
/* Extracts the ALT_LWH2F_AHB_CNTL_DECERR_EN field value from a register. */
#define ALT_LWH2F_AHB_CNTL_DECERR_EN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_LWH2F_AHB_CNTL_DECERR_EN register field value suitable for setting the register. */
#define ALT_LWH2F_AHB_CNTL_DECERR_EN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : force_incr
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                                     
 * :------------------------------------|:------|:-------------------------------------------------
 *  ALT_LWH2F_AHB_CNTL_FORCE_INCR_E_DIS | 0x0   | Multiple outstanding write transactions         
 *  ALT_LWH2F_AHB_CNTL_FORCE_INCR_E_EN  | 0x1   | If a beat is received that has no write data    
 * :                                    |       | strobes set, that write data beat is replaced   
 * :                                    |       | with an IDLE beat. Also, causes all transactions
 * :                                    |       | that are to be output to the AHB domain to be an
 * :                                    |       | undefined length INCR.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_LWH2F_AHB_CNTL_FORCE_INCR
 * 
 * Multiple outstanding write transactions
 */
#define ALT_LWH2F_AHB_CNTL_FORCE_INCR_E_DIS 0x0
/*
 * Enumerated value for register field ALT_LWH2F_AHB_CNTL_FORCE_INCR
 * 
 * If a beat is received that has no write data strobes set, that write data beat
 * is replaced with an IDLE beat. Also, causes all transactions that are to be
 * output to the AHB domain to be an undefined length INCR.
 */
#define ALT_LWH2F_AHB_CNTL_FORCE_INCR_E_EN  0x1

/* The Least Significant Bit (LSB) position of the ALT_LWH2F_AHB_CNTL_FORCE_INCR register field. */
#define ALT_LWH2F_AHB_CNTL_FORCE_INCR_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_AHB_CNTL_FORCE_INCR register field. */
#define ALT_LWH2F_AHB_CNTL_FORCE_INCR_MSB        1
/* The width in bits of the ALT_LWH2F_AHB_CNTL_FORCE_INCR register field. */
#define ALT_LWH2F_AHB_CNTL_FORCE_INCR_WIDTH      1
/* The mask used to set the ALT_LWH2F_AHB_CNTL_FORCE_INCR register field value. */
#define ALT_LWH2F_AHB_CNTL_FORCE_INCR_SET_MSK    0x00000002
/* The mask used to clear the ALT_LWH2F_AHB_CNTL_FORCE_INCR register field value. */
#define ALT_LWH2F_AHB_CNTL_FORCE_INCR_CLR_MSK    0xfffffffd
/* The reset value of the ALT_LWH2F_AHB_CNTL_FORCE_INCR register field. */
#define ALT_LWH2F_AHB_CNTL_FORCE_INCR_RESET      0x0
/* Extracts the ALT_LWH2F_AHB_CNTL_FORCE_INCR field value from a register. */
#define ALT_LWH2F_AHB_CNTL_FORCE_INCR_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_LWH2F_AHB_CNTL_FORCE_INCR register field value suitable for setting the register. */
#define ALT_LWH2F_AHB_CNTL_FORCE_INCR_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_LWH2F_AHB_CNTL.
 */
struct ALT_LWH2F_AHB_CNTL_s
{
    uint32_t  decerr_en  :  1;  /* ALT_LWH2F_AHB_CNTL_DECERR_EN */
    uint32_t  force_incr :  1;  /* ALT_LWH2F_AHB_CNTL_FORCE_INCR */
    uint32_t             : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_LWH2F_AHB_CNTL. */
typedef volatile struct ALT_LWH2F_AHB_CNTL_s  ALT_LWH2F_AHB_CNTL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_LWH2F_AHB_CNTL register from the beginning of the component. */
#define ALT_LWH2F_AHB_CNTL_OFST        0x44
/* The address of the ALT_LWH2F_AHB_CNTL register. */
#define ALT_LWH2F_AHB_CNTL_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_LWH2F_AHB_CNTL_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_LWH2F_MST_F2H.
 */
struct ALT_LWH2F_MST_F2H_s
{
    volatile uint32_t                   _pad_0x0_0x7[2];    /* *UNDEFINED* */
    volatile ALT_LWH2F_FN_MOD_BM_ISS_t  fn_mod_bm_iss;      /* ALT_LWH2F_FN_MOD_BM_ISS */
    volatile uint32_t                   _pad_0xc_0x43[14];  /* *UNDEFINED* */
    volatile ALT_LWH2F_AHB_CNTL_t       ahb_cntl;           /* ALT_LWH2F_AHB_CNTL */
};

/* The typedef declaration for register group ALT_LWH2F_MST_F2H. */
typedef volatile struct ALT_LWH2F_MST_F2H_s  ALT_LWH2F_MST_F2H_t;
/* The struct declaration for the raw register contents of register group ALT_LWH2F_MST_F2H. */
struct ALT_LWH2F_MST_F2H_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];    /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;      /* ALT_LWH2F_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x43[14];  /* *UNDEFINED* */
    volatile uint32_t  ahb_cntl;           /* ALT_LWH2F_AHB_CNTL */
};

/* The typedef declaration for the raw register contents of register group ALT_LWH2F_MST_F2H. */
typedef volatile struct ALT_LWH2F_MST_F2H_raw_s  ALT_LWH2F_MST_F2H_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : HPS2FPGA AXI Bridge Registers - ALT_LWH2F_MST_H2F
 * HPS2FPGA AXI Bridge Registers
 * 
 * Registers associated with the HPS2FPGA master interface.
 * 
 * This master interface provides access to the registers in the HPS2FPGA AXI
 * Bridge.
 * 
 */
#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_LWH2F_MST_H2F.
 */
struct ALT_LWH2F_MST_H2F_s
{
    volatile uint32_t                   _pad_0x0_0x7[2];    /* *UNDEFINED* */
    volatile ALT_LWH2F_FN_MOD_BM_ISS_t  fn_mod_bm_iss;      /* ALT_LWH2F_FN_MOD_BM_ISS */
    volatile uint32_t                   _pad_0xc_0x43[14];  /* *UNDEFINED* */
    volatile ALT_LWH2F_AHB_CNTL_t       ahb_cntl;           /* ALT_LWH2F_AHB_CNTL */
};

/* The typedef declaration for register group ALT_LWH2F_MST_H2F. */
typedef volatile struct ALT_LWH2F_MST_H2F_s  ALT_LWH2F_MST_H2F_t;
/* The struct declaration for the raw register contents of register group ALT_LWH2F_MST_H2F. */
struct ALT_LWH2F_MST_H2F_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];    /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;      /* ALT_LWH2F_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x43[14];  /* *UNDEFINED* */
    volatile uint32_t  ahb_cntl;           /* ALT_LWH2F_AHB_CNTL */
};

/* The typedef declaration for the raw register contents of register group ALT_LWH2F_MST_H2F. */
typedef volatile struct ALT_LWH2F_MST_H2F_raw_s  ALT_LWH2F_MST_H2F_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : 32-bit Master - ALT_LWH2F_MST_B32
 * 32-bit Master
 * 
 * Registers associated with the 32-bit AXI master interface. This master provides
 * access to slaves in the FPGA.
 * 
 */
/*
 * Register : Write Tidemark - wr_tidemark
 * 
 * Controls the release of the transaction in the write data FIFO.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [3:0]  | RW     | 0x4   | Level      
 *  [31:4] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Level - level
 * 
 * Stalls the transaction in the write data FIFO until the number of occupied slots
 * in the write data FIFO exceeds the level. Note that the transaction is released
 * before this level is achieved if the network receives the WLAST beat or the
 * write FIFO becomes full.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_LWH2F_WR_TIDEMARK_LEVEL register field. */
#define ALT_LWH2F_WR_TIDEMARK_LEVEL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_WR_TIDEMARK_LEVEL register field. */
#define ALT_LWH2F_WR_TIDEMARK_LEVEL_MSB        3
/* The width in bits of the ALT_LWH2F_WR_TIDEMARK_LEVEL register field. */
#define ALT_LWH2F_WR_TIDEMARK_LEVEL_WIDTH      4
/* The mask used to set the ALT_LWH2F_WR_TIDEMARK_LEVEL register field value. */
#define ALT_LWH2F_WR_TIDEMARK_LEVEL_SET_MSK    0x0000000f
/* The mask used to clear the ALT_LWH2F_WR_TIDEMARK_LEVEL register field value. */
#define ALT_LWH2F_WR_TIDEMARK_LEVEL_CLR_MSK    0xfffffff0
/* The reset value of the ALT_LWH2F_WR_TIDEMARK_LEVEL register field. */
#define ALT_LWH2F_WR_TIDEMARK_LEVEL_RESET      0x4
/* Extracts the ALT_LWH2F_WR_TIDEMARK_LEVEL field value from a register. */
#define ALT_LWH2F_WR_TIDEMARK_LEVEL_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_LWH2F_WR_TIDEMARK_LEVEL register field value suitable for setting the register. */
#define ALT_LWH2F_WR_TIDEMARK_LEVEL_SET(value) (((value) << 0) & 0x0000000f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_LWH2F_WR_TIDEMARK.
 */
struct ALT_LWH2F_WR_TIDEMARK_s
{
    uint32_t  level :  4;  /* Level */
    uint32_t        : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_LWH2F_WR_TIDEMARK. */
typedef volatile struct ALT_LWH2F_WR_TIDEMARK_s  ALT_LWH2F_WR_TIDEMARK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_LWH2F_WR_TIDEMARK register from the beginning of the component. */
#define ALT_LWH2F_WR_TIDEMARK_OFST        0x40
/* The address of the ALT_LWH2F_WR_TIDEMARK register. */
#define ALT_LWH2F_WR_TIDEMARK_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_LWH2F_WR_TIDEMARK_OFST))

/*
 * Register : Issuing Functionality Modification Register - fn_mod
 * 
 * Sets the block issuing capability to multiple or single outstanding
 * transactions.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description        
 * :-------|:-------|:------|:--------------------
 *  [0]    | RW     | 0x0   | ALT_LWH2F_FN_MOD_RD
 *  [1]    | RW     | 0x0   | ALT_LWH2F_FN_MOD_WR
 *  [31:2] | ???    | 0x0   | *UNDEFINED*        
 * 
 */
/*
 * Field : rd
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description                               
 * :-----------------------------|:------|:-------------------------------------------
 *  ALT_LWH2F_FN_MOD_RD_E_MULT   | 0x0   | Multiple outstanding read transactions    
 *  ALT_LWH2F_FN_MOD_RD_E_SINGLE | 0x1   | Only a single outstanding read transaction
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_LWH2F_FN_MOD_RD
 * 
 * Multiple outstanding read transactions
 */
#define ALT_LWH2F_FN_MOD_RD_E_MULT      0x0
/*
 * Enumerated value for register field ALT_LWH2F_FN_MOD_RD
 * 
 * Only a single outstanding read transaction
 */
#define ALT_LWH2F_FN_MOD_RD_E_SINGLE    0x1

/* The Least Significant Bit (LSB) position of the ALT_LWH2F_FN_MOD_RD register field. */
#define ALT_LWH2F_FN_MOD_RD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_FN_MOD_RD register field. */
#define ALT_LWH2F_FN_MOD_RD_MSB        0
/* The width in bits of the ALT_LWH2F_FN_MOD_RD register field. */
#define ALT_LWH2F_FN_MOD_RD_WIDTH      1
/* The mask used to set the ALT_LWH2F_FN_MOD_RD register field value. */
#define ALT_LWH2F_FN_MOD_RD_SET_MSK    0x00000001
/* The mask used to clear the ALT_LWH2F_FN_MOD_RD register field value. */
#define ALT_LWH2F_FN_MOD_RD_CLR_MSK    0xfffffffe
/* The reset value of the ALT_LWH2F_FN_MOD_RD register field. */
#define ALT_LWH2F_FN_MOD_RD_RESET      0x0
/* Extracts the ALT_LWH2F_FN_MOD_RD field value from a register. */
#define ALT_LWH2F_FN_MOD_RD_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_LWH2F_FN_MOD_RD register field value suitable for setting the register. */
#define ALT_LWH2F_FN_MOD_RD_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : wr
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description                                
 * :-----------------------------|:------|:--------------------------------------------
 *  ALT_LWH2F_FN_MOD_WR_E_MULT   | 0x0   | Multiple outstanding write transactions    
 *  ALT_LWH2F_FN_MOD_WR_E_SINGLE | 0x1   | Only a single outstanding write transaction
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_LWH2F_FN_MOD_WR
 * 
 * Multiple outstanding write transactions
 */
#define ALT_LWH2F_FN_MOD_WR_E_MULT      0x0
/*
 * Enumerated value for register field ALT_LWH2F_FN_MOD_WR
 * 
 * Only a single outstanding write transaction
 */
#define ALT_LWH2F_FN_MOD_WR_E_SINGLE    0x1

/* The Least Significant Bit (LSB) position of the ALT_LWH2F_FN_MOD_WR register field. */
#define ALT_LWH2F_FN_MOD_WR_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_LWH2F_FN_MOD_WR register field. */
#define ALT_LWH2F_FN_MOD_WR_MSB        1
/* The width in bits of the ALT_LWH2F_FN_MOD_WR register field. */
#define ALT_LWH2F_FN_MOD_WR_WIDTH      1
/* The mask used to set the ALT_LWH2F_FN_MOD_WR register field value. */
#define ALT_LWH2F_FN_MOD_WR_SET_MSK    0x00000002
/* The mask used to clear the ALT_LWH2F_FN_MOD_WR register field value. */
#define ALT_LWH2F_FN_MOD_WR_CLR_MSK    0xfffffffd
/* The reset value of the ALT_LWH2F_FN_MOD_WR register field. */
#define ALT_LWH2F_FN_MOD_WR_RESET      0x0
/* Extracts the ALT_LWH2F_FN_MOD_WR field value from a register. */
#define ALT_LWH2F_FN_MOD_WR_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_LWH2F_FN_MOD_WR register field value suitable for setting the register. */
#define ALT_LWH2F_FN_MOD_WR_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_LWH2F_FN_MOD.
 */
struct ALT_LWH2F_FN_MOD_s
{
    uint32_t  rd :  1;  /* ALT_LWH2F_FN_MOD_RD */
    uint32_t  wr :  1;  /* ALT_LWH2F_FN_MOD_WR */
    uint32_t     : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_LWH2F_FN_MOD. */
typedef volatile struct ALT_LWH2F_FN_MOD_s  ALT_LWH2F_FN_MOD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_LWH2F_FN_MOD register from the beginning of the component. */
#define ALT_LWH2F_FN_MOD_OFST        0x108
/* The address of the ALT_LWH2F_FN_MOD register. */
#define ALT_LWH2F_FN_MOD_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_LWH2F_FN_MOD_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_LWH2F_MST_B32.
 */
struct ALT_LWH2F_MST_B32_s
{
    volatile uint32_t                   _pad_0x0_0x7[2];      /* *UNDEFINED* */
    volatile ALT_LWH2F_FN_MOD_BM_ISS_t  fn_mod_bm_iss;        /* ALT_LWH2F_FN_MOD_BM_ISS */
    volatile uint32_t                   _pad_0xc_0x3f[13];    /* *UNDEFINED* */
    volatile ALT_LWH2F_WR_TIDEMARK_t    wr_tidemark;          /* ALT_LWH2F_WR_TIDEMARK */
    volatile uint32_t                   _pad_0x44_0x107[49];  /* *UNDEFINED* */
    volatile ALT_LWH2F_FN_MOD_t         fn_mod;               /* ALT_LWH2F_FN_MOD */
};

/* The typedef declaration for register group ALT_LWH2F_MST_B32. */
typedef volatile struct ALT_LWH2F_MST_B32_s  ALT_LWH2F_MST_B32_t;
/* The struct declaration for the raw register contents of register group ALT_LWH2F_MST_B32. */
struct ALT_LWH2F_MST_B32_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];      /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;        /* ALT_LWH2F_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x3f[13];    /* *UNDEFINED* */
    volatile uint32_t  wr_tidemark;          /* ALT_LWH2F_WR_TIDEMARK */
    volatile uint32_t  _pad_0x44_0x107[49];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod;               /* ALT_LWH2F_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_LWH2F_MST_B32. */
typedef volatile struct ALT_LWH2F_MST_B32_raw_s  ALT_LWH2F_MST_B32_raw_t;
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
 * The struct declaration for register group ALT_LWH2F_MST.
 */
struct ALT_LWH2F_MST_s
{
    volatile ALT_LWH2F_MST_F2H_t  mastergrp_fpga2hpsregs;    /* ALT_LWH2F_MST_F2H */
    volatile uint32_t             _pad_0x48_0xfff[1006];     /* *UNDEFINED* */
    volatile ALT_LWH2F_MST_H2F_t  mastergrp_hps2fpgaregs;    /* ALT_LWH2F_MST_H2F */
    volatile uint32_t             _pad_0x1048_0x2fff[2030];  /* *UNDEFINED* */
    volatile ALT_LWH2F_MST_B32_t  mastergrp_b32;             /* ALT_LWH2F_MST_B32 */
};

/* The typedef declaration for register group ALT_LWH2F_MST. */
typedef volatile struct ALT_LWH2F_MST_s  ALT_LWH2F_MST_t;
/* The struct declaration for the raw register contents of register group ALT_LWH2F_MST. */
struct ALT_LWH2F_MST_raw_s
{
    volatile ALT_LWH2F_MST_F2H_raw_t  mastergrp_fpga2hpsregs;    /* ALT_LWH2F_MST_F2H */
    volatile uint32_t                 _pad_0x48_0xfff[1006];     /* *UNDEFINED* */
    volatile ALT_LWH2F_MST_H2F_raw_t  mastergrp_hps2fpgaregs;    /* ALT_LWH2F_MST_H2F */
    volatile uint32_t                 _pad_0x1048_0x2fff[2030];  /* *UNDEFINED* */
    volatile ALT_LWH2F_MST_B32_raw_t  mastergrp_b32;             /* ALT_LWH2F_MST_B32 */
};

/* The typedef declaration for the raw register contents of register group ALT_LWH2F_MST. */
typedef volatile struct ALT_LWH2F_MST_raw_s  ALT_LWH2F_MST_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : Slave Register Group - ALT_LWH2F_SLV
 * Slave Register Group
 * 
 * Registers associated with slave interfaces.
 * 
 */
/*
 * Register Group : L3 Slave Register Group - ALT_LWH2F_SLV_B32
 * L3 Slave Register Group
 * 
 * Registers associated with the 32-bit AXI slave interface. This slave connects to
 * the L3 Interconnect.
 * 
 */
#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_LWH2F_SLV_B32.
 */
struct ALT_LWH2F_SLV_B32_s
{
    volatile uint32_t            _pad_0x0_0x107[66];  /* *UNDEFINED* */
    volatile ALT_LWH2F_FN_MOD_t  fn_mod;              /* ALT_LWH2F_FN_MOD */
};

/* The typedef declaration for register group ALT_LWH2F_SLV_B32. */
typedef volatile struct ALT_LWH2F_SLV_B32_s  ALT_LWH2F_SLV_B32_t;
/* The struct declaration for the raw register contents of register group ALT_LWH2F_SLV_B32. */
struct ALT_LWH2F_SLV_B32_raw_s
{
    volatile uint32_t  _pad_0x0_0x107[66];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod;              /* ALT_LWH2F_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_LWH2F_SLV_B32. */
typedef volatile struct ALT_LWH2F_SLV_B32_raw_s  ALT_LWH2F_SLV_B32_raw_t;
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
 * The struct declaration for register group ALT_LWH2F_SLV.
 */
struct ALT_LWH2F_SLV_s
{
    volatile uint32_t             _pad_0x0_0x2fff[3072];  /* *UNDEFINED* */
    volatile ALT_LWH2F_SLV_B32_t  slavegrp_b32;           /* ALT_LWH2F_SLV_B32 */
};

/* The typedef declaration for register group ALT_LWH2F_SLV. */
typedef volatile struct ALT_LWH2F_SLV_s  ALT_LWH2F_SLV_t;
/* The struct declaration for the raw register contents of register group ALT_LWH2F_SLV. */
struct ALT_LWH2F_SLV_raw_s
{
    volatile uint32_t                 _pad_0x0_0x2fff[3072];  /* *UNDEFINED* */
    volatile ALT_LWH2F_SLV_B32_raw_t  slavegrp_b32;           /* ALT_LWH2F_SLV_B32 */
};

/* The typedef declaration for the raw register contents of register group ALT_LWH2F_SLV. */
typedef volatile struct ALT_LWH2F_SLV_raw_s  ALT_LWH2F_SLV_raw_t;
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
 * The struct declaration for register group ALT_LWH2F.
 */
struct ALT_LWH2F_s
{
    volatile uint32_t         _pad_0x0_0xfff[1024];         /* *UNDEFINED* */
    volatile ALT_LWH2F_ID_t   idgrp;                        /* ALT_LWH2F_ID */
    volatile ALT_LWH2F_MST_t  mastergrp;                    /* ALT_LWH2F_MST */
    volatile uint32_t         _pad_0x510c_0x41fff[62397];   /* *UNDEFINED* */
    volatile ALT_LWH2F_SLV_t  slavegrp;                     /* ALT_LWH2F_SLV */
    volatile uint32_t         _pad_0x4510c_0x80000[60349];  /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_LWH2F. */
typedef volatile struct ALT_LWH2F_s  ALT_LWH2F_t;
/* The struct declaration for the raw register contents of register group ALT_LWH2F. */
struct ALT_LWH2F_raw_s
{
    volatile uint32_t             _pad_0x0_0xfff[1024];         /* *UNDEFINED* */
    volatile ALT_LWH2F_ID_raw_t   idgrp;                        /* ALT_LWH2F_ID */
    volatile ALT_LWH2F_MST_raw_t  mastergrp;                    /* ALT_LWH2F_MST */
    volatile uint32_t             _pad_0x510c_0x41fff[62397];   /* *UNDEFINED* */
    volatile ALT_LWH2F_SLV_raw_t  slavegrp;                     /* ALT_LWH2F_SLV */
    volatile uint32_t             _pad_0x4510c_0x80000[60349];  /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_LWH2F. */
typedef volatile struct ALT_LWH2F_raw_s  ALT_LWH2F_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_LWH2F_H__ */

