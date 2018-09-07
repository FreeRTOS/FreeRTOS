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

/* Altera - ALT_DAP */

#ifndef __ALTERA_ALT_DAP_H__
#define __ALTERA_ALT_DAP_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : DAP Module Address Space - ALT_DAP
 * DAP Module Address Space
 * 
 * Address space allocated to the DAP. For detailed information about the use of
 * this address space,
 * [url=http://infocenter.arm.com/help/topic/com.arm.doc.ddi0314h/index.html]click
 * here[/url] to access the ARM documentation for the DAP.
 * 
 */
/*
 * Register : Empty - reg
 * 
 * Placeholder
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description
 * :-------|:-------|:--------|:------------
 *  [31:0] | RW     | Unknown | Empty      
 * 
 */
/*
 * Field : Empty - fld
 * 
 * Placeholder
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_DAP_REG_FLD register field. */
#define ALT_DAP_REG_FLD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_DAP_REG_FLD register field. */
#define ALT_DAP_REG_FLD_MSB        31
/* The width in bits of the ALT_DAP_REG_FLD register field. */
#define ALT_DAP_REG_FLD_WIDTH      32
/* The mask used to set the ALT_DAP_REG_FLD register field value. */
#define ALT_DAP_REG_FLD_SET_MSK    0xffffffff
/* The mask used to clear the ALT_DAP_REG_FLD register field value. */
#define ALT_DAP_REG_FLD_CLR_MSK    0x00000000
/* The reset value of the ALT_DAP_REG_FLD register field is UNKNOWN. */
#define ALT_DAP_REG_FLD_RESET      0x0
/* Extracts the ALT_DAP_REG_FLD field value from a register. */
#define ALT_DAP_REG_FLD_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_DAP_REG_FLD register field value suitable for setting the register. */
#define ALT_DAP_REG_FLD_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_DAP_REG.
 */
struct ALT_DAP_REG_s
{
    uint32_t  fld : 32;  /* Empty */
};

/* The typedef declaration for register ALT_DAP_REG. */
typedef volatile struct ALT_DAP_REG_s  ALT_DAP_REG_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_DAP_REG register from the beginning of the component. */
#define ALT_DAP_REG_OFST        0x0

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_DAP.
 */
struct ALT_DAP_s
{
    volatile ALT_DAP_REG_t  reg;  /* ALT_DAP_REG */
};

/* The typedef declaration for register group ALT_DAP. */
typedef volatile struct ALT_DAP_s  ALT_DAP_t;
/* The struct declaration for the raw register contents of register group ALT_DAP. */
struct ALT_DAP_raw_s
{
    volatile uint32_t  reg;  /* ALT_DAP_REG */
};

/* The typedef declaration for the raw register contents of register group ALT_DAP. */
typedef volatile struct ALT_DAP_raw_s  ALT_DAP_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_DAP_H__ */

