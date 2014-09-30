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

/* Altera - ALT_FPGAMGRDATA */

#ifndef __ALTERA_ALT_FPGAMGRDATA_H__
#define __ALTERA_ALT_FPGAMGRDATA_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : FPGA Manager Module Configuration Data - ALT_FPGAMGRDATA
 * FPGA Manager Module Configuration Data
 * 
 * Registers in the FPGA Manager module accessible via its AXI slave
 * 
 */
/*
 * Register : Write Data Register - data
 * 
 * Used to send configuration image to FPGA.
 * 
 * The DATA register accepts 4 bytes of the configuration image on each write. The
 * configuration image byte-stream is converted into a 4-byte word with little-
 * endian ordering. If the configuration image is not an integer multiple of 4
 * bytes, software should pad the configuration image with extra zero bytes to make
 * it an integer multiple of 4 bytes.
 * 
 * The FPGA Manager converts the DATA to 16 bits wide when writing CB.DATA for
 * partial reconfiguration.
 * 
 * The FPGA Manager waits to transmit the data to the CB until the FPGA is able to
 * receive it. For a full configuration, the FPGA Manager waits until the FPGA
 * exits the Reset Phase and enters the Configuration Phase. For a partial
 * reconfiguration, the FPGA Manager waits until the CB.PR_READY signal indicates
 * that the FPGA is ready.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description     
 * :-------|:-------|:--------|:-----------------
 *  [31:0] | RW     | Unknown | Write Data Value
 * 
 */
/*
 * Field : Write Data Value - value
 * 
 * Accepts configuration image to be sent to CB when the HPS configures the FPGA.
 * Software normally just writes this register. If software reads this register, it
 * returns the value 0 and replies with an AXI SLVERR error.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_FPGAMGRDATA_DATA_VALUE register field. */
#define ALT_FPGAMGRDATA_DATA_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGRDATA_DATA_VALUE register field. */
#define ALT_FPGAMGRDATA_DATA_VALUE_MSB        31
/* The width in bits of the ALT_FPGAMGRDATA_DATA_VALUE register field. */
#define ALT_FPGAMGRDATA_DATA_VALUE_WIDTH      32
/* The mask used to set the ALT_FPGAMGRDATA_DATA_VALUE register field value. */
#define ALT_FPGAMGRDATA_DATA_VALUE_SET_MSK    0xffffffff
/* The mask used to clear the ALT_FPGAMGRDATA_DATA_VALUE register field value. */
#define ALT_FPGAMGRDATA_DATA_VALUE_CLR_MSK    0x00000000
/* The reset value of the ALT_FPGAMGRDATA_DATA_VALUE register field is UNKNOWN. */
#define ALT_FPGAMGRDATA_DATA_VALUE_RESET      0x0
/* Extracts the ALT_FPGAMGRDATA_DATA_VALUE field value from a register. */
#define ALT_FPGAMGRDATA_DATA_VALUE_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_FPGAMGRDATA_DATA_VALUE register field value suitable for setting the register. */
#define ALT_FPGAMGRDATA_DATA_VALUE_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_FPGAMGRDATA_DATA.
 */
struct ALT_FPGAMGRDATA_DATA_s
{
    uint32_t  value : 32;  /* Write Data Value */
};

/* The typedef declaration for register ALT_FPGAMGRDATA_DATA. */
typedef volatile struct ALT_FPGAMGRDATA_DATA_s  ALT_FPGAMGRDATA_DATA_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_FPGAMGRDATA_DATA register from the beginning of the component. */
#define ALT_FPGAMGRDATA_DATA_OFST        0x0

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_FPGAMGRDATA.
 */
struct ALT_FPGAMGRDATA_s
{
    volatile ALT_FPGAMGRDATA_DATA_t  data;  /* ALT_FPGAMGRDATA_DATA */
};

/* The typedef declaration for register group ALT_FPGAMGRDATA. */
typedef volatile struct ALT_FPGAMGRDATA_s  ALT_FPGAMGRDATA_t;
/* The struct declaration for the raw register contents of register group ALT_FPGAMGRDATA. */
struct ALT_FPGAMGRDATA_raw_s
{
    volatile uint32_t  data;  /* ALT_FPGAMGRDATA_DATA */
};

/* The typedef declaration for the raw register contents of register group ALT_FPGAMGRDATA. */
typedef volatile struct ALT_FPGAMGRDATA_raw_s  ALT_FPGAMGRDATA_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_FPGAMGRDATA_H__ */

