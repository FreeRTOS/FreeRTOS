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

/* Altera - ALT_GPIO */

#ifndef __ALTERA_ALT_GPIO_H__
#define __ALTERA_ALT_GPIO_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : GPIO Module - ALT_GPIO
 * GPIO Module
 * 
 * Registers in the GPIO module
 * 
 */
/*
 * Register : Port A Data Register - gpio_swporta_dr
 * 
 * This GPIO Data register is used to input or output data
 * 
 * Check the GPIO chapter in the handbook for details on how GPIO2 is implemented.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description
 * :--------|:-------|:------|:------------
 *  [28:0]  | RW     | 0x0   | Port A Data
 *  [31:29] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Port A Data - gpio_swporta_dr
 * 
 * Values written to this register are output on the I/O signals of the GPIO Data
 * Register, if the corresponding data direction bits for GPIO Data Direction Field
 * are set to Output mode. The value read back is equal to the last value written
 * to this register.
 * 
 * Check the GPIO chapter in the handbook for details on how GPIO2 is implemented.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR register field. */
#define ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR register field. */
#define ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR_MSB        28
/* The width in bits of the ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR register field. */
#define ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR_WIDTH      29
/* The mask used to set the ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR register field value. */
#define ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR_SET_MSK    0x1fffffff
/* The mask used to clear the ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR register field value. */
#define ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR_CLR_MSK    0xe0000000
/* The reset value of the ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR register field. */
#define ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR_RESET      0x0
/* Extracts the ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR field value from a register. */
#define ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR_GET(value) (((value) & 0x1fffffff) >> 0)
/* Produces a ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR register field value suitable for setting the register. */
#define ALT_GPIO_SWPORTA_DR_GPIO_SWPORTA_DR_SET(value) (((value) << 0) & 0x1fffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_SWPORTA_DR.
 */
struct ALT_GPIO_SWPORTA_DR_s
{
    uint32_t  gpio_swporta_dr : 29;  /* Port A Data */
    uint32_t                  :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_GPIO_SWPORTA_DR. */
typedef volatile struct ALT_GPIO_SWPORTA_DR_s  ALT_GPIO_SWPORTA_DR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_SWPORTA_DR register from the beginning of the component. */
#define ALT_GPIO_SWPORTA_DR_OFST        0x0
/* The address of the ALT_GPIO_SWPORTA_DR register. */
#define ALT_GPIO_SWPORTA_DR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_SWPORTA_DR_OFST))

/*
 * Register : Port A Data Direction Register - gpio_swporta_ddr
 * 
 * This register establishes the direction of each corresponding GPIO Data Field
 * Bit.
 * 
 * Check the GPIO chapter in the handbook for details on how GPIO2 is implemented.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                
 * :--------|:-------|:------|:----------------------------
 *  [28:0]  | RW     | 0x0   | Port A Data Direction Field
 *  [31:29] | ???    | 0x0   | *UNDEFINED*                
 * 
 */
/*
 * Field : Port A Data Direction Field - gpio_swporta_ddr
 * 
 * Values written to this register independently control the direction of the
 * corresponding data bit in the Port A Data Register.
 * 
 * Check the GPIO chapter in the handbook for details on how GPIO2 is implemented.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                        | Value | Description     
 * :--------------------------------------------|:------|:-----------------
 *  ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR_E_IN  | 0x0   | Input Direction 
 *  ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR_E_OUT | 0x1   | Output Direction
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR
 * 
 * Input Direction
 */
#define ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR_E_IN  0x0
/*
 * Enumerated value for register field ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR
 * 
 * Output Direction
 */
#define ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR_E_OUT 0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR register field. */
#define ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR register field. */
#define ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR_MSB        28
/* The width in bits of the ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR register field. */
#define ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR_WIDTH      29
/* The mask used to set the ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR register field value. */
#define ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR_SET_MSK    0x1fffffff
/* The mask used to clear the ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR register field value. */
#define ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR_CLR_MSK    0xe0000000
/* The reset value of the ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR register field. */
#define ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR_RESET      0x0
/* Extracts the ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR field value from a register. */
#define ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR_GET(value) (((value) & 0x1fffffff) >> 0)
/* Produces a ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR register field value suitable for setting the register. */
#define ALT_GPIO_SWPORTA_DDR_GPIO_SWPORTA_DDR_SET(value) (((value) << 0) & 0x1fffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_SWPORTA_DDR.
 */
struct ALT_GPIO_SWPORTA_DDR_s
{
    uint32_t  gpio_swporta_ddr : 29;  /* Port A Data Direction Field */
    uint32_t                   :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_GPIO_SWPORTA_DDR. */
typedef volatile struct ALT_GPIO_SWPORTA_DDR_s  ALT_GPIO_SWPORTA_DDR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_SWPORTA_DDR register from the beginning of the component. */
#define ALT_GPIO_SWPORTA_DDR_OFST        0x4
/* The address of the ALT_GPIO_SWPORTA_DDR register. */
#define ALT_GPIO_SWPORTA_DDR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_SWPORTA_DDR_OFST))

/*
 * Register : Interrupt Enable Register - gpio_inten
 * 
 * The Interrupt enable register allows interrupts for each bit of the Port A data
 * register.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description           
 * :--------|:-------|:------|:-----------------------
 *  [28:0]  | RW     | 0x0   | Interrupt Enable Field
 *  [31:29] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : Interrupt Enable Field - gpio_inten
 * 
 * Allows each bit of Port A Data Register to be configured for interrupt
 * capability. Interrupts are disabled on the corresponding bits of Port A Data
 * Register if the corresponding data direction register is set to Output.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description                
 * :--------------------------------|:------|:----------------------------
 *  ALT_GPIO_INTEN_GPIO_INTEN_E_DIS | 0x0   | Disable Interrupt on Port A
 *  ALT_GPIO_INTEN_GPIO_INTEN_E_EN  | 0x1   | Enable Interrupt on Port A 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_INTEN_GPIO_INTEN
 * 
 * Disable Interrupt on Port A
 */
#define ALT_GPIO_INTEN_GPIO_INTEN_E_DIS 0x0
/*
 * Enumerated value for register field ALT_GPIO_INTEN_GPIO_INTEN
 * 
 * Enable Interrupt on Port A
 */
#define ALT_GPIO_INTEN_GPIO_INTEN_E_EN  0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_INTEN_GPIO_INTEN register field. */
#define ALT_GPIO_INTEN_GPIO_INTEN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_INTEN_GPIO_INTEN register field. */
#define ALT_GPIO_INTEN_GPIO_INTEN_MSB        28
/* The width in bits of the ALT_GPIO_INTEN_GPIO_INTEN register field. */
#define ALT_GPIO_INTEN_GPIO_INTEN_WIDTH      29
/* The mask used to set the ALT_GPIO_INTEN_GPIO_INTEN register field value. */
#define ALT_GPIO_INTEN_GPIO_INTEN_SET_MSK    0x1fffffff
/* The mask used to clear the ALT_GPIO_INTEN_GPIO_INTEN register field value. */
#define ALT_GPIO_INTEN_GPIO_INTEN_CLR_MSK    0xe0000000
/* The reset value of the ALT_GPIO_INTEN_GPIO_INTEN register field. */
#define ALT_GPIO_INTEN_GPIO_INTEN_RESET      0x0
/* Extracts the ALT_GPIO_INTEN_GPIO_INTEN field value from a register. */
#define ALT_GPIO_INTEN_GPIO_INTEN_GET(value) (((value) & 0x1fffffff) >> 0)
/* Produces a ALT_GPIO_INTEN_GPIO_INTEN register field value suitable for setting the register. */
#define ALT_GPIO_INTEN_GPIO_INTEN_SET(value) (((value) << 0) & 0x1fffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_INTEN.
 */
struct ALT_GPIO_INTEN_s
{
    uint32_t  gpio_inten : 29;  /* Interrupt Enable Field */
    uint32_t             :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_GPIO_INTEN. */
typedef volatile struct ALT_GPIO_INTEN_s  ALT_GPIO_INTEN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_INTEN register from the beginning of the component. */
#define ALT_GPIO_INTEN_OFST        0x30
/* The address of the ALT_GPIO_INTEN register. */
#define ALT_GPIO_INTEN_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_INTEN_OFST))

/*
 * Register : Interrupt Mask Register - gpio_intmask
 * 
 * Controls which pins cause interrupts on Port A Data Register inputs.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description         
 * :--------|:-------|:------|:---------------------
 *  [28:0]  | RW     | 0x0   | Interrupt Mask Field
 *  [31:29] | ???    | 0x0   | *UNDEFINED*         
 * 
 */
/*
 * Field : Interrupt Mask Field - gpio_intmask
 * 
 * Controls whether an interrupt on Port A Data Register can generate an interrupt
 * to the interrupt controller by not masking it. The unmasked status can be read
 * as well as the resultant status after masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                
 * :----------------------------------|:------|:----------------------------
 *  ALT_GPIO_INTMSK_GPIO_INTMSK_E_DIS | 0x0   | Interrupt bits are unmasked
 *  ALT_GPIO_INTMSK_GPIO_INTMSK_E_EN  | 0x1   | Mask Interrupt             
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_INTMSK_GPIO_INTMSK
 * 
 * Interrupt bits are unmasked
 */
#define ALT_GPIO_INTMSK_GPIO_INTMSK_E_DIS   0x0
/*
 * Enumerated value for register field ALT_GPIO_INTMSK_GPIO_INTMSK
 * 
 * Mask Interrupt
 */
#define ALT_GPIO_INTMSK_GPIO_INTMSK_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_INTMSK_GPIO_INTMSK register field. */
#define ALT_GPIO_INTMSK_GPIO_INTMSK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_INTMSK_GPIO_INTMSK register field. */
#define ALT_GPIO_INTMSK_GPIO_INTMSK_MSB        28
/* The width in bits of the ALT_GPIO_INTMSK_GPIO_INTMSK register field. */
#define ALT_GPIO_INTMSK_GPIO_INTMSK_WIDTH      29
/* The mask used to set the ALT_GPIO_INTMSK_GPIO_INTMSK register field value. */
#define ALT_GPIO_INTMSK_GPIO_INTMSK_SET_MSK    0x1fffffff
/* The mask used to clear the ALT_GPIO_INTMSK_GPIO_INTMSK register field value. */
#define ALT_GPIO_INTMSK_GPIO_INTMSK_CLR_MSK    0xe0000000
/* The reset value of the ALT_GPIO_INTMSK_GPIO_INTMSK register field. */
#define ALT_GPIO_INTMSK_GPIO_INTMSK_RESET      0x0
/* Extracts the ALT_GPIO_INTMSK_GPIO_INTMSK field value from a register. */
#define ALT_GPIO_INTMSK_GPIO_INTMSK_GET(value) (((value) & 0x1fffffff) >> 0)
/* Produces a ALT_GPIO_INTMSK_GPIO_INTMSK register field value suitable for setting the register. */
#define ALT_GPIO_INTMSK_GPIO_INTMSK_SET(value) (((value) << 0) & 0x1fffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_INTMSK.
 */
struct ALT_GPIO_INTMSK_s
{
    uint32_t  gpio_intmask : 29;  /* Interrupt Mask Field */
    uint32_t               :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_GPIO_INTMSK. */
typedef volatile struct ALT_GPIO_INTMSK_s  ALT_GPIO_INTMSK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_INTMSK register from the beginning of the component. */
#define ALT_GPIO_INTMSK_OFST        0x34
/* The address of the ALT_GPIO_INTMSK register. */
#define ALT_GPIO_INTMSK_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_INTMSK_OFST))

/*
 * Register : Interrupt Level Register - gpio_inttype_level
 * 
 * The interrupt level register defines the type of interrupt (edge or level).
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description          
 * :--------|:-------|:------|:----------------------
 *  [28:0]  | RW     | 0x0   | Interrupt Level Field
 *  [31:29] | ???    | 0x0   | *UNDEFINED*          
 * 
 */
/*
 * Field : Interrupt Level Field - gpio_inttype_level
 * 
 * This field controls the type of interrupt that can occur on the Port A Data
 * Register.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                              | Value | Description    
 * :--------------------------------------------------|:------|:----------------
 *  ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL_E_LEVEL | 0x0   | Level-sensitive
 *  ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL_E_EDGE  | 0x1   | Edge-sensitive 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL
 * 
 * Level-sensitive
 */
#define ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL_E_LEVEL   0x0
/*
 * Enumerated value for register field ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL
 * 
 * Edge-sensitive
 */
#define ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL_E_EDGE    0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL register field. */
#define ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL register field. */
#define ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL_MSB        28
/* The width in bits of the ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL register field. */
#define ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL_WIDTH      29
/* The mask used to set the ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL register field value. */
#define ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL_SET_MSK    0x1fffffff
/* The mask used to clear the ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL register field value. */
#define ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL_CLR_MSK    0xe0000000
/* The reset value of the ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL register field. */
#define ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL_RESET      0x0
/* Extracts the ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL field value from a register. */
#define ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL_GET(value) (((value) & 0x1fffffff) >> 0)
/* Produces a ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL register field value suitable for setting the register. */
#define ALT_GPIO_INTTYPE_LEVEL_GPIO_INTTYPE_LEVEL_SET(value) (((value) << 0) & 0x1fffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_INTTYPE_LEVEL.
 */
struct ALT_GPIO_INTTYPE_LEVEL_s
{
    uint32_t  gpio_inttype_level : 29;  /* Interrupt Level Field */
    uint32_t                     :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_GPIO_INTTYPE_LEVEL. */
typedef volatile struct ALT_GPIO_INTTYPE_LEVEL_s  ALT_GPIO_INTTYPE_LEVEL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_INTTYPE_LEVEL register from the beginning of the component. */
#define ALT_GPIO_INTTYPE_LEVEL_OFST        0x38
/* The address of the ALT_GPIO_INTTYPE_LEVEL register. */
#define ALT_GPIO_INTTYPE_LEVEL_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_INTTYPE_LEVEL_OFST))

/*
 * Register : Interrupt Polarity Register - gpio_int_polarity
 * 
 * Controls the Polarity of Interrupts that can occur on inputs of Port A Data
 * Register
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description           
 * :--------|:-------|:------|:-----------------------
 *  [28:0]  | RW     | 0x0   | Polarity Control Field
 *  [31:29] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : Polarity Control Field - gpio_int_polarity
 * 
 * Controls the polarity of edge or level sensitivity that can occur on input of
 * Port A Data Register.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                    | Value | Description
 * :----------------------------------------|:------|:------------
 *  ALT_GPIO_INT_POL_GPIO_INT_POL_E_ACTLOW  | 0x0   | Active low 
 *  ALT_GPIO_INT_POL_GPIO_INT_POL_E_ACTHIGH | 0x1   | Active high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_INT_POL_GPIO_INT_POL
 * 
 * Active low
 */
#define ALT_GPIO_INT_POL_GPIO_INT_POL_E_ACTLOW  0x0
/*
 * Enumerated value for register field ALT_GPIO_INT_POL_GPIO_INT_POL
 * 
 * Active high
 */
#define ALT_GPIO_INT_POL_GPIO_INT_POL_E_ACTHIGH 0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_INT_POL_GPIO_INT_POL register field. */
#define ALT_GPIO_INT_POL_GPIO_INT_POL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_INT_POL_GPIO_INT_POL register field. */
#define ALT_GPIO_INT_POL_GPIO_INT_POL_MSB        28
/* The width in bits of the ALT_GPIO_INT_POL_GPIO_INT_POL register field. */
#define ALT_GPIO_INT_POL_GPIO_INT_POL_WIDTH      29
/* The mask used to set the ALT_GPIO_INT_POL_GPIO_INT_POL register field value. */
#define ALT_GPIO_INT_POL_GPIO_INT_POL_SET_MSK    0x1fffffff
/* The mask used to clear the ALT_GPIO_INT_POL_GPIO_INT_POL register field value. */
#define ALT_GPIO_INT_POL_GPIO_INT_POL_CLR_MSK    0xe0000000
/* The reset value of the ALT_GPIO_INT_POL_GPIO_INT_POL register field. */
#define ALT_GPIO_INT_POL_GPIO_INT_POL_RESET      0x0
/* Extracts the ALT_GPIO_INT_POL_GPIO_INT_POL field value from a register. */
#define ALT_GPIO_INT_POL_GPIO_INT_POL_GET(value) (((value) & 0x1fffffff) >> 0)
/* Produces a ALT_GPIO_INT_POL_GPIO_INT_POL register field value suitable for setting the register. */
#define ALT_GPIO_INT_POL_GPIO_INT_POL_SET(value) (((value) << 0) & 0x1fffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_INT_POL.
 */
struct ALT_GPIO_INT_POL_s
{
    uint32_t  gpio_int_polarity : 29;  /* Polarity Control Field */
    uint32_t                    :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_GPIO_INT_POL. */
typedef volatile struct ALT_GPIO_INT_POL_s  ALT_GPIO_INT_POL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_INT_POL register from the beginning of the component. */
#define ALT_GPIO_INT_POL_OFST        0x3c
/* The address of the ALT_GPIO_INT_POL register. */
#define ALT_GPIO_INT_POL_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_INT_POL_OFST))

/*
 * Register : Interrupt Status Register - gpio_intstatus
 * 
 * The Interrupt status is reported for all Port A Data Register Bits.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description           
 * :--------|:-------|:------|:-----------------------
 *  [28:0]  | RW     | 0x0   | Interrupt Status Field
 *  [31:29] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : Interrupt Status Field - gpio_intstatus
 * 
 * Interrupt status of Port A Data Register.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description
 * :--------------------------------------|:------|:------------
 *  ALT_GPIO_INTSTAT_GPIO_INTSTAT_E_INACT | 0x0   | Inactive   
 *  ALT_GPIO_INTSTAT_GPIO_INTSTAT_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_INTSTAT_GPIO_INTSTAT
 * 
 * Inactive
 */
#define ALT_GPIO_INTSTAT_GPIO_INTSTAT_E_INACT   0x0
/*
 * Enumerated value for register field ALT_GPIO_INTSTAT_GPIO_INTSTAT
 * 
 * Active
 */
#define ALT_GPIO_INTSTAT_GPIO_INTSTAT_E_ACT     0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_INTSTAT_GPIO_INTSTAT register field. */
#define ALT_GPIO_INTSTAT_GPIO_INTSTAT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_INTSTAT_GPIO_INTSTAT register field. */
#define ALT_GPIO_INTSTAT_GPIO_INTSTAT_MSB        28
/* The width in bits of the ALT_GPIO_INTSTAT_GPIO_INTSTAT register field. */
#define ALT_GPIO_INTSTAT_GPIO_INTSTAT_WIDTH      29
/* The mask used to set the ALT_GPIO_INTSTAT_GPIO_INTSTAT register field value. */
#define ALT_GPIO_INTSTAT_GPIO_INTSTAT_SET_MSK    0x1fffffff
/* The mask used to clear the ALT_GPIO_INTSTAT_GPIO_INTSTAT register field value. */
#define ALT_GPIO_INTSTAT_GPIO_INTSTAT_CLR_MSK    0xe0000000
/* The reset value of the ALT_GPIO_INTSTAT_GPIO_INTSTAT register field. */
#define ALT_GPIO_INTSTAT_GPIO_INTSTAT_RESET      0x0
/* Extracts the ALT_GPIO_INTSTAT_GPIO_INTSTAT field value from a register. */
#define ALT_GPIO_INTSTAT_GPIO_INTSTAT_GET(value) (((value) & 0x1fffffff) >> 0)
/* Produces a ALT_GPIO_INTSTAT_GPIO_INTSTAT register field value suitable for setting the register. */
#define ALT_GPIO_INTSTAT_GPIO_INTSTAT_SET(value) (((value) << 0) & 0x1fffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_INTSTAT.
 */
struct ALT_GPIO_INTSTAT_s
{
    uint32_t  gpio_intstatus : 29;  /* Interrupt Status Field */
    uint32_t                 :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_GPIO_INTSTAT. */
typedef volatile struct ALT_GPIO_INTSTAT_s  ALT_GPIO_INTSTAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_INTSTAT register from the beginning of the component. */
#define ALT_GPIO_INTSTAT_OFST        0x40
/* The address of the ALT_GPIO_INTSTAT register. */
#define ALT_GPIO_INTSTAT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_INTSTAT_OFST))

/*
 * Register : Raw Interrupt Status Register - gpio_raw_intstatus
 * 
 * This is the Raw Interrupt Status Register for Port A Data Register. It is used
 * with the Interrupt Mask Register to allow interrupts from the Port A Data
 * Register.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description               
 * :--------|:-------|:------|:---------------------------
 *  [28:0]  | RW     | 0x0   | Raw Interrupt Status Field
 *  [31:29] | ???    | 0x0   | *UNDEFINED*               
 * 
 */
/*
 * Field : Raw Interrupt Status Field - gpio_raw_intstatus
 * 
 * Raw interrupt of status of Port A Data Register (premasking bits)
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                          | Value | Description
 * :----------------------------------------------|:------|:------------
 *  ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT_E_INACT | 0x0   | Inactive   
 *  ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT
 * 
 * Inactive
 */
#define ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT_E_INACT   0x0
/*
 * Enumerated value for register field ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT
 * 
 * Active
 */
#define ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT_E_ACT     0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT register field. */
#define ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT register field. */
#define ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT_MSB        28
/* The width in bits of the ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT register field. */
#define ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT_WIDTH      29
/* The mask used to set the ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT register field value. */
#define ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT_SET_MSK    0x1fffffff
/* The mask used to clear the ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT register field value. */
#define ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT_CLR_MSK    0xe0000000
/* The reset value of the ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT register field. */
#define ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT_RESET      0x0
/* Extracts the ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT field value from a register. */
#define ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT_GET(value) (((value) & 0x1fffffff) >> 0)
/* Produces a ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT register field value suitable for setting the register. */
#define ALT_GPIO_RAW_INTSTAT_GPIO_RAW_INTSTAT_SET(value) (((value) << 0) & 0x1fffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_RAW_INTSTAT.
 */
struct ALT_GPIO_RAW_INTSTAT_s
{
    uint32_t  gpio_raw_intstatus : 29;  /* Raw Interrupt Status Field */
    uint32_t                     :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_GPIO_RAW_INTSTAT. */
typedef volatile struct ALT_GPIO_RAW_INTSTAT_s  ALT_GPIO_RAW_INTSTAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_RAW_INTSTAT register from the beginning of the component. */
#define ALT_GPIO_RAW_INTSTAT_OFST        0x44
/* The address of the ALT_GPIO_RAW_INTSTAT register. */
#define ALT_GPIO_RAW_INTSTAT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_RAW_INTSTAT_OFST))

/*
 * Register : Debounce Enable Register - gpio_debounce
 * 
 * Debounces each IO Pin
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                    
 * :--------|:-------|:------|:--------------------------------
 *  [28:0]  | RW     | 0x0   | ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE
 *  [31:29] | ???    | 0x0   | *UNDEFINED*                    
 * 
 */
/*
 * Field : gpio_debounce
 * 
 * Controls whether an external signal that is the source of an interrupt needs to
 * be debounced to remove any spurious glitches. A signal must be valid for two
 * periods of an external clock (gpio_db_clk) before it is internally processed.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description    
 * :--------------------------------------|:------|:----------------
 *  ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE_E_DIS | 0x0   | No debounce    
 *  ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE_E_EN  | 0x1   | Enable debounce
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE
 * 
 * No debounce
 */
#define ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE_E_DIS   0x0
/*
 * Enumerated value for register field ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE
 * 
 * Enable debounce
 */
#define ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE register field. */
#define ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE register field. */
#define ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE_MSB        28
/* The width in bits of the ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE register field. */
#define ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE_WIDTH      29
/* The mask used to set the ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE register field value. */
#define ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE_SET_MSK    0x1fffffff
/* The mask used to clear the ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE register field value. */
#define ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE_CLR_MSK    0xe0000000
/* The reset value of the ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE register field. */
#define ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE_RESET      0x0
/* Extracts the ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE field value from a register. */
#define ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE_GET(value) (((value) & 0x1fffffff) >> 0)
/* Produces a ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE register field value suitable for setting the register. */
#define ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE_SET(value) (((value) << 0) & 0x1fffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_DEBOUNCE.
 */
struct ALT_GPIO_DEBOUNCE_s
{
    uint32_t  gpio_debounce : 29;  /* ALT_GPIO_DEBOUNCE_GPIO_DEBOUNCE */
    uint32_t                :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_GPIO_DEBOUNCE. */
typedef volatile struct ALT_GPIO_DEBOUNCE_s  ALT_GPIO_DEBOUNCE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_DEBOUNCE register from the beginning of the component. */
#define ALT_GPIO_DEBOUNCE_OFST        0x48
/* The address of the ALT_GPIO_DEBOUNCE register. */
#define ALT_GPIO_DEBOUNCE_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_DEBOUNCE_OFST))

/*
 * Register : Clear Interrupt Register - gpio_porta_eoi
 * 
 * Port A Data Register interrupt handling.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                 
 * :--------|:-------|:------|:-----------------------------
 *  [28:0]  | W      | 0x0   | Clears Edge Interrupts Field
 *  [31:29] | ???    | 0x0   | *UNDEFINED*                 
 * 
 */
/*
 * Field : Clears Edge Interrupts Field - gpio_porta_eoi
 * 
 * Controls the clearing of edge type interrupts from the Port A Data Register.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description       
 * :------------------------------------------|:------|:-------------------
 *  ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI_E_NOCLR | 0x0   | No interrupt clear
 *  ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI_E_CLR   | 0x1   | Clear interrupt   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI
 * 
 * No interrupt clear
 */
#define ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI_E_NOCLR   0x0
/*
 * Enumerated value for register field ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI
 * 
 * Clear interrupt
 */
#define ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI_E_CLR     0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI register field. */
#define ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI register field. */
#define ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI_MSB        28
/* The width in bits of the ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI register field. */
#define ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI_WIDTH      29
/* The mask used to set the ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI register field value. */
#define ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI_SET_MSK    0x1fffffff
/* The mask used to clear the ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI register field value. */
#define ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI_CLR_MSK    0xe0000000
/* The reset value of the ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI register field. */
#define ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI_RESET      0x0
/* Extracts the ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI field value from a register. */
#define ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI_GET(value) (((value) & 0x1fffffff) >> 0)
/* Produces a ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI register field value suitable for setting the register. */
#define ALT_GPIO_PORTA_EOI_GPIO_PORTA_EOI_SET(value) (((value) << 0) & 0x1fffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_PORTA_EOI.
 */
struct ALT_GPIO_PORTA_EOI_s
{
    uint32_t  gpio_porta_eoi : 29;  /* Clears Edge Interrupts Field */
    uint32_t                 :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_GPIO_PORTA_EOI. */
typedef volatile struct ALT_GPIO_PORTA_EOI_s  ALT_GPIO_PORTA_EOI_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_PORTA_EOI register from the beginning of the component. */
#define ALT_GPIO_PORTA_EOI_OFST        0x4c
/* The address of the ALT_GPIO_PORTA_EOI register. */
#define ALT_GPIO_PORTA_EOI_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_PORTA_EOI_OFST))

/*
 * Register : External Port A Register - gpio_ext_porta
 * 
 * The external port register is used to input data to the metastability flops.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description        
 * :--------|:-------|:------|:--------------------
 *  [28:0]  | R      | 0x0   | External Port Field
 *  [31:29] | ???    | 0x0   | *UNDEFINED*        
 * 
 */
/*
 * Field : External Port Field - gpio_ext_porta
 * 
 * When Port A Data Register is configured as Input, then reading this location
 * reads the values on the signals. When the data direction of Port A Data Register
 * is set as Output, reading this location reads Port A Data Register
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA register field. */
#define ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA register field. */
#define ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA_MSB        28
/* The width in bits of the ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA register field. */
#define ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA_WIDTH      29
/* The mask used to set the ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA register field value. */
#define ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA_SET_MSK    0x1fffffff
/* The mask used to clear the ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA register field value. */
#define ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA_CLR_MSK    0xe0000000
/* The reset value of the ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA register field. */
#define ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA_RESET      0x0
/* Extracts the ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA field value from a register. */
#define ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA_GET(value) (((value) & 0x1fffffff) >> 0)
/* Produces a ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA register field value suitable for setting the register. */
#define ALT_GPIO_EXT_PORTA_GPIO_EXT_PORTA_SET(value) (((value) << 0) & 0x1fffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_EXT_PORTA.
 */
struct ALT_GPIO_EXT_PORTA_s
{
    const uint32_t  gpio_ext_porta : 29;  /* External Port Field */
    uint32_t                       :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_GPIO_EXT_PORTA. */
typedef volatile struct ALT_GPIO_EXT_PORTA_s  ALT_GPIO_EXT_PORTA_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_EXT_PORTA register from the beginning of the component. */
#define ALT_GPIO_EXT_PORTA_OFST        0x50
/* The address of the ALT_GPIO_EXT_PORTA register. */
#define ALT_GPIO_EXT_PORTA_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_EXT_PORTA_OFST))

/*
 * Register : Synchronization Level Register - gpio_ls_sync
 * 
 * The Synchronization level register is used to synchronize input with l4_mp_clk
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                
 * :-------|:-------|:------|:----------------------------
 *  [0]    | RW     | 0x0   | Synchronization Level Field
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                
 * 
 */
/*
 * Field : Synchronization Level Field - gpio_ls_sync
 * 
 * The level-sensitive interrupts is synchronized to l4_mp_clk.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description                    
 * :---------------------------------------|:------|:--------------------------------
 *  ALT_GPIO_LS_SYNC_GPIO_LS_SYNC_E_NOSYNC | 0x0   | No synchronization to l4_mp_clk
 *  ALT_GPIO_LS_SYNC_GPIO_LS_SYNC_E_SYNC   | 0x1   | Synchronize to l4_mp_clk       
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_LS_SYNC_GPIO_LS_SYNC
 * 
 * No synchronization to l4_mp_clk
 */
#define ALT_GPIO_LS_SYNC_GPIO_LS_SYNC_E_NOSYNC  0x0
/*
 * Enumerated value for register field ALT_GPIO_LS_SYNC_GPIO_LS_SYNC
 * 
 * Synchronize to l4_mp_clk
 */
#define ALT_GPIO_LS_SYNC_GPIO_LS_SYNC_E_SYNC    0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_LS_SYNC_GPIO_LS_SYNC register field. */
#define ALT_GPIO_LS_SYNC_GPIO_LS_SYNC_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_LS_SYNC_GPIO_LS_SYNC register field. */
#define ALT_GPIO_LS_SYNC_GPIO_LS_SYNC_MSB        0
/* The width in bits of the ALT_GPIO_LS_SYNC_GPIO_LS_SYNC register field. */
#define ALT_GPIO_LS_SYNC_GPIO_LS_SYNC_WIDTH      1
/* The mask used to set the ALT_GPIO_LS_SYNC_GPIO_LS_SYNC register field value. */
#define ALT_GPIO_LS_SYNC_GPIO_LS_SYNC_SET_MSK    0x00000001
/* The mask used to clear the ALT_GPIO_LS_SYNC_GPIO_LS_SYNC register field value. */
#define ALT_GPIO_LS_SYNC_GPIO_LS_SYNC_CLR_MSK    0xfffffffe
/* The reset value of the ALT_GPIO_LS_SYNC_GPIO_LS_SYNC register field. */
#define ALT_GPIO_LS_SYNC_GPIO_LS_SYNC_RESET      0x0
/* Extracts the ALT_GPIO_LS_SYNC_GPIO_LS_SYNC field value from a register. */
#define ALT_GPIO_LS_SYNC_GPIO_LS_SYNC_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_GPIO_LS_SYNC_GPIO_LS_SYNC register field value suitable for setting the register. */
#define ALT_GPIO_LS_SYNC_GPIO_LS_SYNC_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_LS_SYNC.
 */
struct ALT_GPIO_LS_SYNC_s
{
    uint32_t  gpio_ls_sync :  1;  /* Synchronization Level Field */
    uint32_t               : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_GPIO_LS_SYNC. */
typedef volatile struct ALT_GPIO_LS_SYNC_s  ALT_GPIO_LS_SYNC_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_LS_SYNC register from the beginning of the component. */
#define ALT_GPIO_LS_SYNC_OFST        0x60
/* The address of the ALT_GPIO_LS_SYNC register. */
#define ALT_GPIO_LS_SYNC_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_LS_SYNC_OFST))

/*
 * Register : ID Code Register - gpio_id_code
 * 
 * GPIO ID code.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description  
 * :-------|:-------|:------|:--------------
 *  [31:0] | R      | 0x0   | ID Code Field
 * 
 */
/*
 * Field : ID Code Field - gpio_id_code
 * 
 * Chip identification
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_GPIO_ID_CODE_GPIO_ID_CODE register field. */
#define ALT_GPIO_ID_CODE_GPIO_ID_CODE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_ID_CODE_GPIO_ID_CODE register field. */
#define ALT_GPIO_ID_CODE_GPIO_ID_CODE_MSB        31
/* The width in bits of the ALT_GPIO_ID_CODE_GPIO_ID_CODE register field. */
#define ALT_GPIO_ID_CODE_GPIO_ID_CODE_WIDTH      32
/* The mask used to set the ALT_GPIO_ID_CODE_GPIO_ID_CODE register field value. */
#define ALT_GPIO_ID_CODE_GPIO_ID_CODE_SET_MSK    0xffffffff
/* The mask used to clear the ALT_GPIO_ID_CODE_GPIO_ID_CODE register field value. */
#define ALT_GPIO_ID_CODE_GPIO_ID_CODE_CLR_MSK    0x00000000
/* The reset value of the ALT_GPIO_ID_CODE_GPIO_ID_CODE register field. */
#define ALT_GPIO_ID_CODE_GPIO_ID_CODE_RESET      0x0
/* Extracts the ALT_GPIO_ID_CODE_GPIO_ID_CODE field value from a register. */
#define ALT_GPIO_ID_CODE_GPIO_ID_CODE_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_GPIO_ID_CODE_GPIO_ID_CODE register field value suitable for setting the register. */
#define ALT_GPIO_ID_CODE_GPIO_ID_CODE_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_ID_CODE.
 */
struct ALT_GPIO_ID_CODE_s
{
    const uint32_t  gpio_id_code : 32;  /* ID Code Field */
};

/* The typedef declaration for register ALT_GPIO_ID_CODE. */
typedef volatile struct ALT_GPIO_ID_CODE_s  ALT_GPIO_ID_CODE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_ID_CODE register from the beginning of the component. */
#define ALT_GPIO_ID_CODE_OFST        0x64
/* The address of the ALT_GPIO_ID_CODE register. */
#define ALT_GPIO_ID_CODE_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_ID_CODE_OFST))

/*
 * Register : GPIO Version Register - gpio_ver_id_code
 * 
 * GPIO Component Version
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset      | Description                  
 * :-------|:-------|:-----------|:------------------------------
 *  [31:0] | R      | 0x3230382a | ASCII Component Version Field
 * 
 */
/*
 * Field : ASCII Component Version Field - gpio_ver_id_code
 * 
 * ASCII value for each number in the version, followed by *. For example.
 * 32_30_31_2A represents the version 2.01
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE register field. */
#define ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE register field. */
#define ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_MSB        31
/* The width in bits of the ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE register field. */
#define ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_WIDTH      32
/* The mask used to set the ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE register field value. */
#define ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_SET_MSK    0xffffffff
/* The mask used to clear the ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE register field value. */
#define ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_CLR_MSK    0x00000000
/* The reset value of the ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE register field. */
#define ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_RESET      0x3230382a
/* Extracts the ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE field value from a register. */
#define ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE register field value suitable for setting the register. */
#define ALT_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_VER_ID_CODE.
 */
struct ALT_GPIO_VER_ID_CODE_s
{
    const uint32_t  gpio_ver_id_code : 32;  /* ASCII Component Version Field */
};

/* The typedef declaration for register ALT_GPIO_VER_ID_CODE. */
typedef volatile struct ALT_GPIO_VER_ID_CODE_s  ALT_GPIO_VER_ID_CODE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_VER_ID_CODE register from the beginning of the component. */
#define ALT_GPIO_VER_ID_CODE_OFST        0x6c
/* The address of the ALT_GPIO_VER_ID_CODE register. */
#define ALT_GPIO_VER_ID_CODE_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_VER_ID_CODE_OFST))

/*
 * Register : Configuration Register 2 - gpio_config_reg2
 * 
 * Specifies the bit width of port A.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description          
 * :--------|:-------|:------|:----------------------
 *  [4:0]   | R      | 0x1c  | Port A Width (less 1)
 *  [9:5]   | R      | 0x7   | Port B Width (less 1)
 *  [14:10] | R      | 0x7   | Port C Width (less 1)
 *  [19:15] | R      | 0x7   | Port D Width (less 1)
 *  [31:20] | ???    | 0x0   | *UNDEFINED*          
 * 
 */
/*
 * Field : Port A Width (less 1) - encoded_id_pwidth_a
 * 
 * Specifies the width of GPIO Port A. The value 28 represents the 29-bit width
 * less one.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                   | Value | Description              
 * :-------------------------------------------------------|:------|:--------------------------
 *  ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_E_WIDTHLESSONE8BITS  | 0x7   | Width (less 1) of 8 bits 
 *  ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_E_WIDTHLESSONE29BITS | 0x1c  | Width (less 1) of 29 bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A
 * 
 * Width (less 1) of 8 bits
 */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_E_WIDTHLESSONE8BITS   0x7
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A
 * 
 * Width (less 1) of 29 bits
 */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_E_WIDTHLESSONE29BITS  0x1c

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_MSB        4
/* The width in bits of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_WIDTH      5
/* The mask used to set the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A register field value. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_SET_MSK    0x0000001f
/* The mask used to clear the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A register field value. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_CLR_MSK    0xffffffe0
/* The reset value of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_RESET      0x1c
/* Extracts the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A field value from a register. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_GET(value) (((value) & 0x0000001f) >> 0)
/* Produces a ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_SET(value) (((value) << 0) & 0x0000001f)

/*
 * Field : Port B Width (less 1) - encoded_id_pwidth_b
 * 
 * Specifies the width of GPIO Port B. Ignored because there is no Port B in the
 * GPIO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                   | Value | Description              
 * :-------------------------------------------------------|:------|:--------------------------
 *  ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_E_WIDTHLESSONE8BITS  | 0x7   | Width (less 1) of 8 bits 
 *  ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_E_WIDTHLESSONE29BITS | 0x1c  | Width (less 1) of 29 bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B
 * 
 * Width (less 1) of 8 bits
 */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_E_WIDTHLESSONE8BITS   0x7
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B
 * 
 * Width (less 1) of 29 bits
 */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_E_WIDTHLESSONE29BITS  0x1c

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_MSB        9
/* The width in bits of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_WIDTH      5
/* The mask used to set the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B register field value. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_SET_MSK    0x000003e0
/* The mask used to clear the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B register field value. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_CLR_MSK    0xfffffc1f
/* The reset value of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_RESET      0x7
/* Extracts the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B field value from a register. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_GET(value) (((value) & 0x000003e0) >> 5)
/* Produces a ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_SET(value) (((value) << 5) & 0x000003e0)

/*
 * Field : Port C Width (less 1) - encoded_id_pwidth_c
 * 
 * Specifies the width of GPIO Port C. Ignored because there is no Port C in the
 * GPIO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                   | Value | Description              
 * :-------------------------------------------------------|:------|:--------------------------
 *  ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_E_WIDTHLESSONE8BITS  | 0x7   | Width (less 1) of 8 bits 
 *  ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_E_WIDTHLESSONE29BITS | 0x1c  | Width (less 1) of 29 bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C
 * 
 * Width (less 1) of 8 bits
 */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_E_WIDTHLESSONE8BITS   0x7
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C
 * 
 * Width (less 1) of 29 bits
 */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_E_WIDTHLESSONE29BITS  0x1c

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_MSB        14
/* The width in bits of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_WIDTH      5
/* The mask used to set the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C register field value. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_SET_MSK    0x00007c00
/* The mask used to clear the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C register field value. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_CLR_MSK    0xffff83ff
/* The reset value of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_RESET      0x7
/* Extracts the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C field value from a register. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_GET(value) (((value) & 0x00007c00) >> 10)
/* Produces a ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_SET(value) (((value) << 10) & 0x00007c00)

/*
 * Field : Port D Width (less 1) - encoded_id_pwidth_d
 * 
 * Specifies the width of GPIO Port D. Ignored because there is no Port D in the
 * GPIO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                   | Value | Description              
 * :-------------------------------------------------------|:------|:--------------------------
 *  ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_E_WIDTHLESSONE8BITS  | 0x7   | Width (less 1) of 8 bits 
 *  ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_E_WIDTHLESSONE29BITS | 0x1c  | Width (less 1) of 29 bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D
 * 
 * Width (less 1) of 8 bits
 */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_E_WIDTHLESSONE8BITS   0x7
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D
 * 
 * Width (less 1) of 29 bits
 */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_E_WIDTHLESSONE29BITS  0x1c

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_MSB        19
/* The width in bits of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_WIDTH      5
/* The mask used to set the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D register field value. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_SET_MSK    0x000f8000
/* The mask used to clear the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D register field value. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_CLR_MSK    0xfff07fff
/* The reset value of the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D register field. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_RESET      0x7
/* Extracts the ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D field value from a register. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_GET(value) (((value) & 0x000f8000) >> 15)
/* Produces a ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_SET(value) (((value) << 15) & 0x000f8000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_CFG_REG2.
 */
struct ALT_GPIO_CFG_REG2_s
{
    const uint32_t  encoded_id_pwidth_a :  5;  /* Port A Width (less 1) */
    const uint32_t  encoded_id_pwidth_b :  5;  /* Port B Width (less 1) */
    const uint32_t  encoded_id_pwidth_c :  5;  /* Port C Width (less 1) */
    const uint32_t  encoded_id_pwidth_d :  5;  /* Port D Width (less 1) */
    uint32_t                            : 12;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_GPIO_CFG_REG2. */
typedef volatile struct ALT_GPIO_CFG_REG2_s  ALT_GPIO_CFG_REG2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_CFG_REG2 register from the beginning of the component. */
#define ALT_GPIO_CFG_REG2_OFST        0x70
/* The address of the ALT_GPIO_CFG_REG2 register. */
#define ALT_GPIO_CFG_REG2_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_CFG_REG2_OFST))

/*
 * Register : Configuration Register 1 - gpio_config_reg1
 * 
 * Reports settings of various GPIO configuration parameters
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                      
 * :--------|:-------|:------|:----------------------------------
 *  [1:0]   | R      | 0x2   | APB DATA WIDTH                   
 *  [3:2]   | R      | 0x0   | NUM PORTS                        
 *  [4]     | R      | 0x1   | PORT A SINGLE CTL                
 *  [5]     | R      | 0x1   | PORT B SINGLE CTL                
 *  [6]     | R      | 0x1   | PORT C SINGLE CTL                
 *  [7]     | R      | 0x1   | PORT D SINGLE CTL                
 *  [8]     | R      | 0x0   | HW PORTA                         
 *  [11:9]  | ???    | 0x0   | *UNDEFINED*                      
 *  [12]    | R      | 0x1   | Port A Interrupt Field           
 *  [13]    | R      | 0x1   | Debounce Field                   
 *  [14]    | R      | 0x1   | Encoded GPIO Parameters Available
 *  [15]    | R      | 0x1   | ID Field                         
 *  [20:16] | R      | 0x1f  | Encoded ID Width Field           
 *  [31:21] | ???    | 0x0   | *UNDEFINED*                      
 * 
 */
/*
 * Field : APB DATA WIDTH - apb_data_width
 * 
 * Fixed to support an ABP data bus width of 32-bits.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                           | Value | Description             
 * :-----------------------------------------------|:------|:-------------------------
 *  ALT_GPIO_CFG_REG1_APB_DATA_WIDTH_E_WIDTH32BITS | 0x2   | APB Data Width = 32-bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG1_APB_DATA_WIDTH
 * 
 * APB Data Width = 32-bits
 */
#define ALT_GPIO_CFG_REG1_APB_DATA_WIDTH_E_WIDTH32BITS  0x2

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG1_APB_DATA_WIDTH register field. */
#define ALT_GPIO_CFG_REG1_APB_DATA_WIDTH_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG1_APB_DATA_WIDTH register field. */
#define ALT_GPIO_CFG_REG1_APB_DATA_WIDTH_MSB        1
/* The width in bits of the ALT_GPIO_CFG_REG1_APB_DATA_WIDTH register field. */
#define ALT_GPIO_CFG_REG1_APB_DATA_WIDTH_WIDTH      2
/* The mask used to set the ALT_GPIO_CFG_REG1_APB_DATA_WIDTH register field value. */
#define ALT_GPIO_CFG_REG1_APB_DATA_WIDTH_SET_MSK    0x00000003
/* The mask used to clear the ALT_GPIO_CFG_REG1_APB_DATA_WIDTH register field value. */
#define ALT_GPIO_CFG_REG1_APB_DATA_WIDTH_CLR_MSK    0xfffffffc
/* The reset value of the ALT_GPIO_CFG_REG1_APB_DATA_WIDTH register field. */
#define ALT_GPIO_CFG_REG1_APB_DATA_WIDTH_RESET      0x2
/* Extracts the ALT_GPIO_CFG_REG1_APB_DATA_WIDTH field value from a register. */
#define ALT_GPIO_CFG_REG1_APB_DATA_WIDTH_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_GPIO_CFG_REG1_APB_DATA_WIDTH register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG1_APB_DATA_WIDTH_SET(value) (((value) << 0) & 0x00000003)

/*
 * Field : NUM PORTS - num_ports
 * 
 * The value of this register is fixed at one port (Port A).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description             
 * :---------------------------------------|:------|:-------------------------
 *  ALT_GPIO_CFG_REG1_NUM_PORTS_E_ONEPORTA | 0x0   | Number of GPIO Ports = 1
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG1_NUM_PORTS
 * 
 * Number of GPIO Ports = 1
 */
#define ALT_GPIO_CFG_REG1_NUM_PORTS_E_ONEPORTA  0x0

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG1_NUM_PORTS register field. */
#define ALT_GPIO_CFG_REG1_NUM_PORTS_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG1_NUM_PORTS register field. */
#define ALT_GPIO_CFG_REG1_NUM_PORTS_MSB        3
/* The width in bits of the ALT_GPIO_CFG_REG1_NUM_PORTS register field. */
#define ALT_GPIO_CFG_REG1_NUM_PORTS_WIDTH      2
/* The mask used to set the ALT_GPIO_CFG_REG1_NUM_PORTS register field value. */
#define ALT_GPIO_CFG_REG1_NUM_PORTS_SET_MSK    0x0000000c
/* The mask used to clear the ALT_GPIO_CFG_REG1_NUM_PORTS register field value. */
#define ALT_GPIO_CFG_REG1_NUM_PORTS_CLR_MSK    0xfffffff3
/* The reset value of the ALT_GPIO_CFG_REG1_NUM_PORTS register field. */
#define ALT_GPIO_CFG_REG1_NUM_PORTS_RESET      0x0
/* Extracts the ALT_GPIO_CFG_REG1_NUM_PORTS field value from a register. */
#define ALT_GPIO_CFG_REG1_NUM_PORTS_GET(value) (((value) & 0x0000000c) >> 2)
/* Produces a ALT_GPIO_CFG_REG1_NUM_PORTS register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG1_NUM_PORTS_SET(value) (((value) << 2) & 0x0000000c)

/*
 * Field : PORT A SINGLE CTL - porta_single_ctl
 * 
 * Indicates the mode of operation of Port A to be software controlled only.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                             | Value | Description                             
 * :-------------------------------------------------|:------|:-----------------------------------------
 *  ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL_E_SOFTCTLONLY | 0x1   | Software Enabled Individual Port Control
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL
 * 
 * Software Enabled Individual Port Control
 */
#define ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL_E_SOFTCTLONLY    0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL_MSB        4
/* The width in bits of the ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL_WIDTH      1
/* The mask used to set the ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL register field value. */
#define ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL_SET_MSK    0x00000010
/* The mask used to clear the ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL register field value. */
#define ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL_CLR_MSK    0xffffffef
/* The reset value of the ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL_RESET      0x1
/* Extracts the ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL field value from a register. */
#define ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG1_PORTA_SINGLE_CTL_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : PORT B SINGLE CTL - portb_single_ctl
 * 
 * Indicates the mode of operation of Port B to be software controlled only.
 * Ignored because there is no Port B in the GPIO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                             | Value | Description                             
 * :-------------------------------------------------|:------|:-----------------------------------------
 *  ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL_E_SOFTCTLONLY | 0x1   | Software Enabled Individual Port Control
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL
 * 
 * Software Enabled Individual Port Control
 */
#define ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL_E_SOFTCTLONLY    0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL_MSB        5
/* The width in bits of the ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL_WIDTH      1
/* The mask used to set the ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL register field value. */
#define ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL_SET_MSK    0x00000020
/* The mask used to clear the ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL register field value. */
#define ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL_CLR_MSK    0xffffffdf
/* The reset value of the ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL_RESET      0x1
/* Extracts the ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL field value from a register. */
#define ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG1_PORTB_SINGLE_CTL_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : PORT C SINGLE CTL - portc_single_ctl
 * 
 * Indicates the mode of operation of Port C to be software controlled only.
 * Ignored because there is no Port C in the GPIO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                             | Value | Description                             
 * :-------------------------------------------------|:------|:-----------------------------------------
 *  ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL_E_SOFTCTLONLY | 0x1   | Software Enabled Individual Port Control
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL
 * 
 * Software Enabled Individual Port Control
 */
#define ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL_E_SOFTCTLONLY    0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL_MSB        6
/* The width in bits of the ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL_WIDTH      1
/* The mask used to set the ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL register field value. */
#define ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL_SET_MSK    0x00000040
/* The mask used to clear the ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL register field value. */
#define ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL_CLR_MSK    0xffffffbf
/* The reset value of the ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL_RESET      0x1
/* Extracts the ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL field value from a register. */
#define ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG1_PORTC_SINGLE_CTL_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : PORT D SINGLE CTL - portd_single_ctl
 * 
 * Indicates the mode of operation of Port D to be software controlled only.
 * Ignored because there is no Port D in the GPIO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                             | Value | Description                             
 * :-------------------------------------------------|:------|:-----------------------------------------
 *  ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL_E_SOFTCTLONLY | 0x1   | Software Enabled Individual Port Control
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL
 * 
 * Software Enabled Individual Port Control
 */
#define ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL_E_SOFTCTLONLY    0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL_MSB        7
/* The width in bits of the ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL_WIDTH      1
/* The mask used to set the ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL register field value. */
#define ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL_SET_MSK    0x00000080
/* The mask used to clear the ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL register field value. */
#define ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL_CLR_MSK    0xffffff7f
/* The reset value of the ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL register field. */
#define ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL_RESET      0x1
/* Extracts the ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL field value from a register. */
#define ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG1_PORTD_SINGLE_CTL_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : HW PORTA - hw_porta
 * 
 * The value is fixed to enable Port A configuration to be controlled by software
 * only.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                     | Value | Description                           
 * :-----------------------------------------|:------|:---------------------------------------
 *  ALT_GPIO_CFG_REG1_HW_PORTA_E_PORTANOHARD | 0x0   | Software Configuration Control Enabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG1_HW_PORTA
 * 
 * Software Configuration Control Enabled
 */
#define ALT_GPIO_CFG_REG1_HW_PORTA_E_PORTANOHARD    0x0

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG1_HW_PORTA register field. */
#define ALT_GPIO_CFG_REG1_HW_PORTA_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG1_HW_PORTA register field. */
#define ALT_GPIO_CFG_REG1_HW_PORTA_MSB        8
/* The width in bits of the ALT_GPIO_CFG_REG1_HW_PORTA register field. */
#define ALT_GPIO_CFG_REG1_HW_PORTA_WIDTH      1
/* The mask used to set the ALT_GPIO_CFG_REG1_HW_PORTA register field value. */
#define ALT_GPIO_CFG_REG1_HW_PORTA_SET_MSK    0x00000100
/* The mask used to clear the ALT_GPIO_CFG_REG1_HW_PORTA register field value. */
#define ALT_GPIO_CFG_REG1_HW_PORTA_CLR_MSK    0xfffffeff
/* The reset value of the ALT_GPIO_CFG_REG1_HW_PORTA register field. */
#define ALT_GPIO_CFG_REG1_HW_PORTA_RESET      0x0
/* Extracts the ALT_GPIO_CFG_REG1_HW_PORTA field value from a register. */
#define ALT_GPIO_CFG_REG1_HW_PORTA_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_GPIO_CFG_REG1_HW_PORTA register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG1_HW_PORTA_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Port A Interrupt Field - porta_intr
 * 
 * The value of this field is fixed to allow interrupts on Port A.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                       | Value | Description              
 * :-------------------------------------------|:------|:--------------------------
 *  ALT_GPIO_CFG_REG1_PORTA_INTR_E_PORTAINTERR | 0x1   | Port A Interrupts Enabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG1_PORTA_INTR
 * 
 * Port A Interrupts Enabled
 */
#define ALT_GPIO_CFG_REG1_PORTA_INTR_E_PORTAINTERR  0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG1_PORTA_INTR register field. */
#define ALT_GPIO_CFG_REG1_PORTA_INTR_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG1_PORTA_INTR register field. */
#define ALT_GPIO_CFG_REG1_PORTA_INTR_MSB        12
/* The width in bits of the ALT_GPIO_CFG_REG1_PORTA_INTR register field. */
#define ALT_GPIO_CFG_REG1_PORTA_INTR_WIDTH      1
/* The mask used to set the ALT_GPIO_CFG_REG1_PORTA_INTR register field value. */
#define ALT_GPIO_CFG_REG1_PORTA_INTR_SET_MSK    0x00001000
/* The mask used to clear the ALT_GPIO_CFG_REG1_PORTA_INTR register field value. */
#define ALT_GPIO_CFG_REG1_PORTA_INTR_CLR_MSK    0xffffefff
/* The reset value of the ALT_GPIO_CFG_REG1_PORTA_INTR register field. */
#define ALT_GPIO_CFG_REG1_PORTA_INTR_RESET      0x1
/* Extracts the ALT_GPIO_CFG_REG1_PORTA_INTR field value from a register. */
#define ALT_GPIO_CFG_REG1_PORTA_INTR_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_GPIO_CFG_REG1_PORTA_INTR register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG1_PORTA_INTR_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : Debounce Field - debounce
 * 
 * The value of this field is fixed to allow debouncing of the Port A signals.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description        
 * :---------------------------------------|:------|:--------------------
 *  ALT_GPIO_CFG_REG1_DEBOUNCE_E_DEBOUNCEA | 0x1   | Debounce is Enabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG1_DEBOUNCE
 * 
 * Debounce is Enabled
 */
#define ALT_GPIO_CFG_REG1_DEBOUNCE_E_DEBOUNCEA  0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG1_DEBOUNCE register field. */
#define ALT_GPIO_CFG_REG1_DEBOUNCE_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG1_DEBOUNCE register field. */
#define ALT_GPIO_CFG_REG1_DEBOUNCE_MSB        13
/* The width in bits of the ALT_GPIO_CFG_REG1_DEBOUNCE register field. */
#define ALT_GPIO_CFG_REG1_DEBOUNCE_WIDTH      1
/* The mask used to set the ALT_GPIO_CFG_REG1_DEBOUNCE register field value. */
#define ALT_GPIO_CFG_REG1_DEBOUNCE_SET_MSK    0x00002000
/* The mask used to clear the ALT_GPIO_CFG_REG1_DEBOUNCE register field value. */
#define ALT_GPIO_CFG_REG1_DEBOUNCE_CLR_MSK    0xffffdfff
/* The reset value of the ALT_GPIO_CFG_REG1_DEBOUNCE register field. */
#define ALT_GPIO_CFG_REG1_DEBOUNCE_RESET      0x1
/* Extracts the ALT_GPIO_CFG_REG1_DEBOUNCE field value from a register. */
#define ALT_GPIO_CFG_REG1_DEBOUNCE_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_GPIO_CFG_REG1_DEBOUNCE register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG1_DEBOUNCE_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : Encoded GPIO Parameters Available - add_encoded_params
 * 
 * Fixed to allow the indentification of the Designware IP component.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                            | Value | Description              
 * :------------------------------------------------|:------|:--------------------------
 *  ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS_E_ADDENCPARAMS | 0x1   | Enable IP indentification
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS
 * 
 * Enable IP indentification
 */
#define ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS_E_ADDENCPARAMS 0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS register field. */
#define ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS register field. */
#define ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS_MSB        14
/* The width in bits of the ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS register field. */
#define ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS_WIDTH      1
/* The mask used to set the ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS register field value. */
#define ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS_SET_MSK    0x00004000
/* The mask used to clear the ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS register field value. */
#define ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS_CLR_MSK    0xffffbfff
/* The reset value of the ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS register field. */
#define ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS_RESET      0x1
/* Extracts the ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS field value from a register. */
#define ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG1_ADD_ENC_PARAMS_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : ID Field - gpio_id
 * 
 * Provides an ID code value
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description 
 * :-----------------------------------|:------|:-------------
 *  ALT_GPIO_CFG_REG1_GPIO_ID_E_IDCODE | 0x1   | GPIO ID Code
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG1_GPIO_ID
 * 
 * GPIO ID Code
 */
#define ALT_GPIO_CFG_REG1_GPIO_ID_E_IDCODE  0x1

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG1_GPIO_ID register field. */
#define ALT_GPIO_CFG_REG1_GPIO_ID_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG1_GPIO_ID register field. */
#define ALT_GPIO_CFG_REG1_GPIO_ID_MSB        15
/* The width in bits of the ALT_GPIO_CFG_REG1_GPIO_ID register field. */
#define ALT_GPIO_CFG_REG1_GPIO_ID_WIDTH      1
/* The mask used to set the ALT_GPIO_CFG_REG1_GPIO_ID register field value. */
#define ALT_GPIO_CFG_REG1_GPIO_ID_SET_MSK    0x00008000
/* The mask used to clear the ALT_GPIO_CFG_REG1_GPIO_ID register field value. */
#define ALT_GPIO_CFG_REG1_GPIO_ID_CLR_MSK    0xffff7fff
/* The reset value of the ALT_GPIO_CFG_REG1_GPIO_ID register field. */
#define ALT_GPIO_CFG_REG1_GPIO_ID_RESET      0x1
/* Extracts the ALT_GPIO_CFG_REG1_GPIO_ID field value from a register. */
#define ALT_GPIO_CFG_REG1_GPIO_ID_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_GPIO_CFG_REG1_GPIO_ID register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG1_GPIO_ID_SET(value) (((value) << 15) & 0x00008000)

/*
 * Field : Encoded ID Width Field - encoded_id_width
 * 
 * This value is fixed at 32 bits.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                        | Value | Description      
 * :--------------------------------------------|:------|:------------------
 *  ALT_GPIO_CFG_REG1_ENC_ID_WIDTH_E_ENCIDWIDTH | 0x1f  | Width of ID Field
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_GPIO_CFG_REG1_ENC_ID_WIDTH
 * 
 * Width of ID Field
 */
#define ALT_GPIO_CFG_REG1_ENC_ID_WIDTH_E_ENCIDWIDTH 0x1f

/* The Least Significant Bit (LSB) position of the ALT_GPIO_CFG_REG1_ENC_ID_WIDTH register field. */
#define ALT_GPIO_CFG_REG1_ENC_ID_WIDTH_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_GPIO_CFG_REG1_ENC_ID_WIDTH register field. */
#define ALT_GPIO_CFG_REG1_ENC_ID_WIDTH_MSB        20
/* The width in bits of the ALT_GPIO_CFG_REG1_ENC_ID_WIDTH register field. */
#define ALT_GPIO_CFG_REG1_ENC_ID_WIDTH_WIDTH      5
/* The mask used to set the ALT_GPIO_CFG_REG1_ENC_ID_WIDTH register field value. */
#define ALT_GPIO_CFG_REG1_ENC_ID_WIDTH_SET_MSK    0x001f0000
/* The mask used to clear the ALT_GPIO_CFG_REG1_ENC_ID_WIDTH register field value. */
#define ALT_GPIO_CFG_REG1_ENC_ID_WIDTH_CLR_MSK    0xffe0ffff
/* The reset value of the ALT_GPIO_CFG_REG1_ENC_ID_WIDTH register field. */
#define ALT_GPIO_CFG_REG1_ENC_ID_WIDTH_RESET      0x1f
/* Extracts the ALT_GPIO_CFG_REG1_ENC_ID_WIDTH field value from a register. */
#define ALT_GPIO_CFG_REG1_ENC_ID_WIDTH_GET(value) (((value) & 0x001f0000) >> 16)
/* Produces a ALT_GPIO_CFG_REG1_ENC_ID_WIDTH register field value suitable for setting the register. */
#define ALT_GPIO_CFG_REG1_ENC_ID_WIDTH_SET(value) (((value) << 16) & 0x001f0000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_GPIO_CFG_REG1.
 */
struct ALT_GPIO_CFG_REG1_s
{
    const uint32_t  apb_data_width     :  2;  /* APB DATA WIDTH */
    const uint32_t  num_ports          :  2;  /* NUM PORTS */
    const uint32_t  porta_single_ctl   :  1;  /* PORT A SINGLE CTL */
    const uint32_t  portb_single_ctl   :  1;  /* PORT B SINGLE CTL */
    const uint32_t  portc_single_ctl   :  1;  /* PORT C SINGLE CTL */
    const uint32_t  portd_single_ctl   :  1;  /* PORT D SINGLE CTL */
    const uint32_t  hw_porta           :  1;  /* HW PORTA */
    uint32_t                           :  3;  /* *UNDEFINED* */
    const uint32_t  porta_intr         :  1;  /* Port A Interrupt Field */
    const uint32_t  debounce           :  1;  /* Debounce Field */
    const uint32_t  add_encoded_params :  1;  /* Encoded GPIO Parameters Available */
    const uint32_t  gpio_id            :  1;  /* ID Field */
    const uint32_t  encoded_id_width   :  5;  /* Encoded ID Width Field */
    uint32_t                           : 11;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_GPIO_CFG_REG1. */
typedef volatile struct ALT_GPIO_CFG_REG1_s  ALT_GPIO_CFG_REG1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_GPIO_CFG_REG1 register from the beginning of the component. */
#define ALT_GPIO_CFG_REG1_OFST        0x74
/* The address of the ALT_GPIO_CFG_REG1 register. */
#define ALT_GPIO_CFG_REG1_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_GPIO_CFG_REG1_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_GPIO.
 */
struct ALT_GPIO_s
{
    volatile ALT_GPIO_SWPORTA_DR_t     gpio_swporta_dr;     /* ALT_GPIO_SWPORTA_DR */
    volatile ALT_GPIO_SWPORTA_DDR_t    gpio_swporta_ddr;    /* ALT_GPIO_SWPORTA_DDR */
    volatile uint32_t                  _pad_0x8_0x2f[10];   /* *UNDEFINED* */
    volatile ALT_GPIO_INTEN_t          gpio_inten;          /* ALT_GPIO_INTEN */
    volatile ALT_GPIO_INTMSK_t         gpio_intmask;        /* ALT_GPIO_INTMSK */
    volatile ALT_GPIO_INTTYPE_LEVEL_t  gpio_inttype_level;  /* ALT_GPIO_INTTYPE_LEVEL */
    volatile ALT_GPIO_INT_POL_t        gpio_int_polarity;   /* ALT_GPIO_INT_POL */
    volatile ALT_GPIO_INTSTAT_t        gpio_intstatus;      /* ALT_GPIO_INTSTAT */
    volatile ALT_GPIO_RAW_INTSTAT_t    gpio_raw_intstatus;  /* ALT_GPIO_RAW_INTSTAT */
    volatile ALT_GPIO_DEBOUNCE_t       gpio_debounce;       /* ALT_GPIO_DEBOUNCE */
    volatile ALT_GPIO_PORTA_EOI_t      gpio_porta_eoi;      /* ALT_GPIO_PORTA_EOI */
    volatile ALT_GPIO_EXT_PORTA_t      gpio_ext_porta;      /* ALT_GPIO_EXT_PORTA */
    volatile uint32_t                  _pad_0x54_0x5f[3];   /* *UNDEFINED* */
    volatile ALT_GPIO_LS_SYNC_t        gpio_ls_sync;        /* ALT_GPIO_LS_SYNC */
    volatile ALT_GPIO_ID_CODE_t        gpio_id_code;        /* ALT_GPIO_ID_CODE */
    volatile uint32_t                  _pad_0x68_0x6b;      /* *UNDEFINED* */
    volatile ALT_GPIO_VER_ID_CODE_t    gpio_ver_id_code;    /* ALT_GPIO_VER_ID_CODE */
    volatile ALT_GPIO_CFG_REG2_t       gpio_config_reg2;    /* ALT_GPIO_CFG_REG2 */
    volatile ALT_GPIO_CFG_REG1_t       gpio_config_reg1;    /* ALT_GPIO_CFG_REG1 */
    volatile uint32_t                  _pad_0x78_0x80[2];   /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_GPIO. */
typedef volatile struct ALT_GPIO_s  ALT_GPIO_t;
/* The struct declaration for the raw register contents of register group ALT_GPIO. */
struct ALT_GPIO_raw_s
{
    volatile uint32_t  gpio_swporta_dr;     /* ALT_GPIO_SWPORTA_DR */
    volatile uint32_t  gpio_swporta_ddr;    /* ALT_GPIO_SWPORTA_DDR */
    volatile uint32_t  _pad_0x8_0x2f[10];   /* *UNDEFINED* */
    volatile uint32_t  gpio_inten;          /* ALT_GPIO_INTEN */
    volatile uint32_t  gpio_intmask;        /* ALT_GPIO_INTMSK */
    volatile uint32_t  gpio_inttype_level;  /* ALT_GPIO_INTTYPE_LEVEL */
    volatile uint32_t  gpio_int_polarity;   /* ALT_GPIO_INT_POL */
    volatile uint32_t  gpio_intstatus;      /* ALT_GPIO_INTSTAT */
    volatile uint32_t  gpio_raw_intstatus;  /* ALT_GPIO_RAW_INTSTAT */
    volatile uint32_t  gpio_debounce;       /* ALT_GPIO_DEBOUNCE */
    volatile uint32_t  gpio_porta_eoi;      /* ALT_GPIO_PORTA_EOI */
    volatile uint32_t  gpio_ext_porta;      /* ALT_GPIO_EXT_PORTA */
    volatile uint32_t  _pad_0x54_0x5f[3];   /* *UNDEFINED* */
    volatile uint32_t  gpio_ls_sync;        /* ALT_GPIO_LS_SYNC */
    volatile uint32_t  gpio_id_code;        /* ALT_GPIO_ID_CODE */
    volatile uint32_t  _pad_0x68_0x6b;      /* *UNDEFINED* */
    volatile uint32_t  gpio_ver_id_code;    /* ALT_GPIO_VER_ID_CODE */
    volatile uint32_t  gpio_config_reg2;    /* ALT_GPIO_CFG_REG2 */
    volatile uint32_t  gpio_config_reg1;    /* ALT_GPIO_CFG_REG1 */
    volatile uint32_t  _pad_0x78_0x80[2];   /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_GPIO. */
typedef volatile struct ALT_GPIO_raw_s  ALT_GPIO_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_GPIO_H__ */

