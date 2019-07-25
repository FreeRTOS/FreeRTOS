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

/* Altera - ALT_ACPIDMAP */

#ifndef __ALTERA_ALT_ACPIDMAP_H__
#define __ALTERA_ALT_ACPIDMAP_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : ACP ID Mapper Registers - ALT_ACPIDMAP
 * ACP ID Mapper Registers
 * 
 * Registers in the ACP ID Mapper module
 * 
 */
/*
 * Register : Read AXI Master Mapping Register for Fixed Virtual ID 2 - vid2rd
 * 
 * The Read AXI Master Mapping Register contains the USER, ADDR page, and ID
 * signals mapping values for particular transaction with 12-bit ID which locks the
 * fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                 
 * :--------|:-------|:------|:-----------------------------
 *  [3:0]   | ???    | 0x0   | *UNDEFINED*                 
 *  [8:4]   | RW     | 0x1   | ARUSER value to SCU for ID=2
 *  [11:9]  | ???    | 0x0   | *UNDEFINED*                 
 *  [13:12] | RW     | 0x0   | ARADDR 1GB Page Decoder     
 *  [15:14] | ???    | 0x0   | *UNDEFINED*                 
 *  [27:16] | RW     | 0x4   | Remap Master ID = DAP ID    
 *  [30:28] | ???    | 0x0   | *UNDEFINED*                 
 *  [31]    | RW     | 0x1   | Force Mapping for ID=2      
 * 
 */
/*
 * Field : ARUSER value to SCU for ID=2 - user
 * 
 * This value is propagated to SCU as ARUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2RD_USER register field. */
#define ALT_ACPIDMAP_VID2RD_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2RD_USER register field. */
#define ALT_ACPIDMAP_VID2RD_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID2RD_USER register field. */
#define ALT_ACPIDMAP_VID2RD_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID2RD_USER register field value. */
#define ALT_ACPIDMAP_VID2RD_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID2RD_USER register field value. */
#define ALT_ACPIDMAP_VID2RD_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID2RD_USER register field. */
#define ALT_ACPIDMAP_VID2RD_USER_RESET      0x1
/* Extracts the ALT_ACPIDMAP_VID2RD_USER field value from a register. */
#define ALT_ACPIDMAP_VID2RD_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID2RD_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2RD_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : ARADDR 1GB Page Decoder - page
 * 
 * ARADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2RD_PAGE register field. */
#define ALT_ACPIDMAP_VID2RD_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2RD_PAGE register field. */
#define ALT_ACPIDMAP_VID2RD_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID2RD_PAGE register field. */
#define ALT_ACPIDMAP_VID2RD_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID2RD_PAGE register field value. */
#define ALT_ACPIDMAP_VID2RD_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID2RD_PAGE register field value. */
#define ALT_ACPIDMAP_VID2RD_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID2RD_PAGE register field. */
#define ALT_ACPIDMAP_VID2RD_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID2RD_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID2RD_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID2RD_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2RD_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID = DAP ID - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2RD_MID register field. */
#define ALT_ACPIDMAP_VID2RD_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2RD_MID register field. */
#define ALT_ACPIDMAP_VID2RD_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID2RD_MID register field. */
#define ALT_ACPIDMAP_VID2RD_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID2RD_MID register field value. */
#define ALT_ACPIDMAP_VID2RD_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID2RD_MID register field value. */
#define ALT_ACPIDMAP_VID2RD_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID2RD_MID register field. */
#define ALT_ACPIDMAP_VID2RD_MID_RESET      0x4
/* Extracts the ALT_ACPIDMAP_VID2RD_MID field value from a register. */
#define ALT_ACPIDMAP_VID2RD_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID2RD_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2RD_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping for ID=2 - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2RD_FORCE register field. */
#define ALT_ACPIDMAP_VID2RD_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2RD_FORCE register field. */
#define ALT_ACPIDMAP_VID2RD_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID2RD_FORCE register field. */
#define ALT_ACPIDMAP_VID2RD_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID2RD_FORCE register field value. */
#define ALT_ACPIDMAP_VID2RD_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID2RD_FORCE register field value. */
#define ALT_ACPIDMAP_VID2RD_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID2RD_FORCE register field. */
#define ALT_ACPIDMAP_VID2RD_FORCE_RESET      0x1
/* Extracts the ALT_ACPIDMAP_VID2RD_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID2RD_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID2RD_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2RD_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID2RD.
 */
struct ALT_ACPIDMAP_VID2RD_s
{
    uint32_t        :  4;  /* *UNDEFINED* */
    uint32_t  user  :  5;  /* ARUSER value to SCU for ID=2 */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  page  :  2;  /* ARADDR 1GB Page Decoder */
    uint32_t        :  2;  /* *UNDEFINED* */
    uint32_t  mid   : 12;  /* Remap Master ID = DAP ID */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  force :  1;  /* Force Mapping for ID=2 */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID2RD. */
typedef volatile struct ALT_ACPIDMAP_VID2RD_s  ALT_ACPIDMAP_VID2RD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID2RD register from the beginning of the component. */
#define ALT_ACPIDMAP_VID2RD_OFST        0x0

/*
 * Register : Write AXI Master Mapping Register for Fixed Virtual ID 2 - vid2wr
 * 
 * The Write AXI Master Mapping Register contains the USER, ADDR page, and ID
 * signals mapping values for particular transaction with 12-bit ID which locks the
 * fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                 
 * :--------|:-------|:------|:-----------------------------
 *  [3:0]   | ???    | 0x0   | *UNDEFINED*                 
 *  [8:4]   | RW     | 0x1   | AWUSER value to SCU for ID=2
 *  [11:9]  | ???    | 0x0   | *UNDEFINED*                 
 *  [13:12] | RW     | 0x0   | AWADDR 1GB Page Decoder     
 *  [15:14] | ???    | 0x0   | *UNDEFINED*                 
 *  [27:16] | RW     | 0x4   | Remap Master ID = DAP ID    
 *  [30:28] | ???    | 0x0   | *UNDEFINED*                 
 *  [31]    | RW     | 0x1   | Force Mapping for ID=2      
 * 
 */
/*
 * Field : AWUSER value to SCU for ID=2 - user
 * 
 * This value is propagated to SCU as AWUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2WR_USER register field. */
#define ALT_ACPIDMAP_VID2WR_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2WR_USER register field. */
#define ALT_ACPIDMAP_VID2WR_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID2WR_USER register field. */
#define ALT_ACPIDMAP_VID2WR_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID2WR_USER register field value. */
#define ALT_ACPIDMAP_VID2WR_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID2WR_USER register field value. */
#define ALT_ACPIDMAP_VID2WR_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID2WR_USER register field. */
#define ALT_ACPIDMAP_VID2WR_USER_RESET      0x1
/* Extracts the ALT_ACPIDMAP_VID2WR_USER field value from a register. */
#define ALT_ACPIDMAP_VID2WR_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID2WR_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2WR_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : AWADDR 1GB Page Decoder - page
 * 
 * AWADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2WR_PAGE register field. */
#define ALT_ACPIDMAP_VID2WR_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2WR_PAGE register field. */
#define ALT_ACPIDMAP_VID2WR_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID2WR_PAGE register field. */
#define ALT_ACPIDMAP_VID2WR_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID2WR_PAGE register field value. */
#define ALT_ACPIDMAP_VID2WR_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID2WR_PAGE register field value. */
#define ALT_ACPIDMAP_VID2WR_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID2WR_PAGE register field. */
#define ALT_ACPIDMAP_VID2WR_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID2WR_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID2WR_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID2WR_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2WR_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID = DAP ID - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2WR_MID register field. */
#define ALT_ACPIDMAP_VID2WR_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2WR_MID register field. */
#define ALT_ACPIDMAP_VID2WR_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID2WR_MID register field. */
#define ALT_ACPIDMAP_VID2WR_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID2WR_MID register field value. */
#define ALT_ACPIDMAP_VID2WR_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID2WR_MID register field value. */
#define ALT_ACPIDMAP_VID2WR_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID2WR_MID register field. */
#define ALT_ACPIDMAP_VID2WR_MID_RESET      0x4
/* Extracts the ALT_ACPIDMAP_VID2WR_MID field value from a register. */
#define ALT_ACPIDMAP_VID2WR_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID2WR_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2WR_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping for ID=2 - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2WR_FORCE register field. */
#define ALT_ACPIDMAP_VID2WR_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2WR_FORCE register field. */
#define ALT_ACPIDMAP_VID2WR_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID2WR_FORCE register field. */
#define ALT_ACPIDMAP_VID2WR_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID2WR_FORCE register field value. */
#define ALT_ACPIDMAP_VID2WR_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID2WR_FORCE register field value. */
#define ALT_ACPIDMAP_VID2WR_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID2WR_FORCE register field. */
#define ALT_ACPIDMAP_VID2WR_FORCE_RESET      0x1
/* Extracts the ALT_ACPIDMAP_VID2WR_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID2WR_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID2WR_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2WR_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID2WR.
 */
struct ALT_ACPIDMAP_VID2WR_s
{
    uint32_t        :  4;  /* *UNDEFINED* */
    uint32_t  user  :  5;  /* AWUSER value to SCU for ID=2 */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  page  :  2;  /* AWADDR 1GB Page Decoder */
    uint32_t        :  2;  /* *UNDEFINED* */
    uint32_t  mid   : 12;  /* Remap Master ID = DAP ID */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  force :  1;  /* Force Mapping for ID=2 */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID2WR. */
typedef volatile struct ALT_ACPIDMAP_VID2WR_s  ALT_ACPIDMAP_VID2WR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID2WR register from the beginning of the component. */
#define ALT_ACPIDMAP_VID2WR_OFST        0x4

/*
 * Register : Read AXI Master Mapping Register for Fixed Virtual ID 3 - vid3rd
 * 
 * The Read AXI Master Mapping Register contains the USER, ADDR page, and ID
 * signals mapping values for particular transaction with 12-bit ID which locks the
 * fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description            
 * :--------|:-------|:------|:------------------------
 *  [3:0]   | ???    | 0x0   | *UNDEFINED*            
 *  [8:4]   | RW     | 0x0   | ARUSER value to SCU    
 *  [11:9]  | ???    | 0x0   | *UNDEFINED*            
 *  [13:12] | RW     | 0x0   | ARADDR 1GB Page Decoder
 *  [15:14] | ???    | 0x0   | *UNDEFINED*            
 *  [27:16] | RW     | 0x0   | Remap Master ID        
 *  [30:28] | ???    | 0x0   | *UNDEFINED*            
 *  [31]    | RW     | 0x0   | Force Mapping          
 * 
 */
/*
 * Field : ARUSER value to SCU - user
 * 
 * This value is propagated to SCU as ARUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3RD_USER register field. */
#define ALT_ACPIDMAP_VID3RD_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3RD_USER register field. */
#define ALT_ACPIDMAP_VID3RD_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID3RD_USER register field. */
#define ALT_ACPIDMAP_VID3RD_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID3RD_USER register field value. */
#define ALT_ACPIDMAP_VID3RD_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID3RD_USER register field value. */
#define ALT_ACPIDMAP_VID3RD_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID3RD_USER register field. */
#define ALT_ACPIDMAP_VID3RD_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3RD_USER field value from a register. */
#define ALT_ACPIDMAP_VID3RD_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID3RD_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3RD_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : ARADDR 1GB Page Decoder - page
 * 
 * ARADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3RD_PAGE register field. */
#define ALT_ACPIDMAP_VID3RD_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3RD_PAGE register field. */
#define ALT_ACPIDMAP_VID3RD_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID3RD_PAGE register field. */
#define ALT_ACPIDMAP_VID3RD_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID3RD_PAGE register field value. */
#define ALT_ACPIDMAP_VID3RD_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID3RD_PAGE register field value. */
#define ALT_ACPIDMAP_VID3RD_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID3RD_PAGE register field. */
#define ALT_ACPIDMAP_VID3RD_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3RD_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID3RD_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID3RD_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3RD_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3RD_MID register field. */
#define ALT_ACPIDMAP_VID3RD_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3RD_MID register field. */
#define ALT_ACPIDMAP_VID3RD_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID3RD_MID register field. */
#define ALT_ACPIDMAP_VID3RD_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID3RD_MID register field value. */
#define ALT_ACPIDMAP_VID3RD_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID3RD_MID register field value. */
#define ALT_ACPIDMAP_VID3RD_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID3RD_MID register field. */
#define ALT_ACPIDMAP_VID3RD_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3RD_MID field value from a register. */
#define ALT_ACPIDMAP_VID3RD_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID3RD_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3RD_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3RD_FORCE register field. */
#define ALT_ACPIDMAP_VID3RD_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3RD_FORCE register field. */
#define ALT_ACPIDMAP_VID3RD_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID3RD_FORCE register field. */
#define ALT_ACPIDMAP_VID3RD_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID3RD_FORCE register field value. */
#define ALT_ACPIDMAP_VID3RD_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID3RD_FORCE register field value. */
#define ALT_ACPIDMAP_VID3RD_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID3RD_FORCE register field. */
#define ALT_ACPIDMAP_VID3RD_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3RD_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID3RD_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID3RD_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3RD_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID3RD.
 */
struct ALT_ACPIDMAP_VID3RD_s
{
    uint32_t        :  4;  /* *UNDEFINED* */
    uint32_t  user  :  5;  /* ARUSER value to SCU */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  page  :  2;  /* ARADDR 1GB Page Decoder */
    uint32_t        :  2;  /* *UNDEFINED* */
    uint32_t  mid   : 12;  /* Remap Master ID */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  force :  1;  /* Force Mapping */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID3RD. */
typedef volatile struct ALT_ACPIDMAP_VID3RD_s  ALT_ACPIDMAP_VID3RD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID3RD register from the beginning of the component. */
#define ALT_ACPIDMAP_VID3RD_OFST        0x8

/*
 * Register : Write AXI Master Mapping Register for Fixed Virtual ID 3 - vid3wr
 * 
 * The Write AXI Master Mapping Register contains the USER, ADDR page, and ID
 * signals mapping values for particular transaction with 12-bit ID which locks the
 * fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description            
 * :--------|:-------|:------|:------------------------
 *  [3:0]   | ???    | 0x0   | *UNDEFINED*            
 *  [8:4]   | RW     | 0x0   | AWUSER value to SCU    
 *  [11:9]  | ???    | 0x0   | *UNDEFINED*            
 *  [13:12] | RW     | 0x0   | AWADDR 1GB Page Decoder
 *  [15:14] | ???    | 0x0   | *UNDEFINED*            
 *  [27:16] | RW     | 0x0   | Remap Master ID        
 *  [30:28] | ???    | 0x0   | *UNDEFINED*            
 *  [31]    | RW     | 0x0   | Force Mapping          
 * 
 */
/*
 * Field : AWUSER value to SCU - user
 * 
 * This value is propagated to SCU as AWUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3WR_USER register field. */
#define ALT_ACPIDMAP_VID3WR_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3WR_USER register field. */
#define ALT_ACPIDMAP_VID3WR_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID3WR_USER register field. */
#define ALT_ACPIDMAP_VID3WR_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID3WR_USER register field value. */
#define ALT_ACPIDMAP_VID3WR_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID3WR_USER register field value. */
#define ALT_ACPIDMAP_VID3WR_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID3WR_USER register field. */
#define ALT_ACPIDMAP_VID3WR_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3WR_USER field value from a register. */
#define ALT_ACPIDMAP_VID3WR_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID3WR_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3WR_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : AWADDR 1GB Page Decoder - page
 * 
 * AWADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3WR_PAGE register field. */
#define ALT_ACPIDMAP_VID3WR_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3WR_PAGE register field. */
#define ALT_ACPIDMAP_VID3WR_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID3WR_PAGE register field. */
#define ALT_ACPIDMAP_VID3WR_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID3WR_PAGE register field value. */
#define ALT_ACPIDMAP_VID3WR_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID3WR_PAGE register field value. */
#define ALT_ACPIDMAP_VID3WR_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID3WR_PAGE register field. */
#define ALT_ACPIDMAP_VID3WR_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3WR_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID3WR_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID3WR_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3WR_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3WR_MID register field. */
#define ALT_ACPIDMAP_VID3WR_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3WR_MID register field. */
#define ALT_ACPIDMAP_VID3WR_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID3WR_MID register field. */
#define ALT_ACPIDMAP_VID3WR_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID3WR_MID register field value. */
#define ALT_ACPIDMAP_VID3WR_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID3WR_MID register field value. */
#define ALT_ACPIDMAP_VID3WR_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID3WR_MID register field. */
#define ALT_ACPIDMAP_VID3WR_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3WR_MID field value from a register. */
#define ALT_ACPIDMAP_VID3WR_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID3WR_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3WR_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3WR_FORCE register field. */
#define ALT_ACPIDMAP_VID3WR_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3WR_FORCE register field. */
#define ALT_ACPIDMAP_VID3WR_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID3WR_FORCE register field. */
#define ALT_ACPIDMAP_VID3WR_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID3WR_FORCE register field value. */
#define ALT_ACPIDMAP_VID3WR_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID3WR_FORCE register field value. */
#define ALT_ACPIDMAP_VID3WR_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID3WR_FORCE register field. */
#define ALT_ACPIDMAP_VID3WR_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3WR_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID3WR_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID3WR_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3WR_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID3WR.
 */
struct ALT_ACPIDMAP_VID3WR_s
{
    uint32_t        :  4;  /* *UNDEFINED* */
    uint32_t  user  :  5;  /* AWUSER value to SCU */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  page  :  2;  /* AWADDR 1GB Page Decoder */
    uint32_t        :  2;  /* *UNDEFINED* */
    uint32_t  mid   : 12;  /* Remap Master ID */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  force :  1;  /* Force Mapping */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID3WR. */
typedef volatile struct ALT_ACPIDMAP_VID3WR_s  ALT_ACPIDMAP_VID3WR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID3WR register from the beginning of the component. */
#define ALT_ACPIDMAP_VID3WR_OFST        0xc

/*
 * Register : Read AXI Master Mapping Register for Fixed Virtual ID 4 - vid4rd
 * 
 * The Read AXI Master Mapping Register contains the USER, ADDR page, and ID
 * signals mapping values for particular transaction with 12-bit ID which locks the
 * fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description            
 * :--------|:-------|:------|:------------------------
 *  [3:0]   | ???    | 0x0   | *UNDEFINED*            
 *  [8:4]   | RW     | 0x0   | ARUSER value to SCU    
 *  [11:9]  | ???    | 0x0   | *UNDEFINED*            
 *  [13:12] | RW     | 0x0   | ARADDR 1GB Page Decoder
 *  [15:14] | ???    | 0x0   | *UNDEFINED*            
 *  [27:16] | RW     | 0x0   | Remap Master ID        
 *  [30:28] | ???    | 0x0   | *UNDEFINED*            
 *  [31]    | RW     | 0x0   | Force Mapping          
 * 
 */
/*
 * Field : ARUSER value to SCU - user
 * 
 * This value is propagated to SCU as ARUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4RD_USER register field. */
#define ALT_ACPIDMAP_VID4RD_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4RD_USER register field. */
#define ALT_ACPIDMAP_VID4RD_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID4RD_USER register field. */
#define ALT_ACPIDMAP_VID4RD_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID4RD_USER register field value. */
#define ALT_ACPIDMAP_VID4RD_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID4RD_USER register field value. */
#define ALT_ACPIDMAP_VID4RD_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID4RD_USER register field. */
#define ALT_ACPIDMAP_VID4RD_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4RD_USER field value from a register. */
#define ALT_ACPIDMAP_VID4RD_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID4RD_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4RD_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : ARADDR 1GB Page Decoder - page
 * 
 * ARADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4RD_PAGE register field. */
#define ALT_ACPIDMAP_VID4RD_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4RD_PAGE register field. */
#define ALT_ACPIDMAP_VID4RD_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID4RD_PAGE register field. */
#define ALT_ACPIDMAP_VID4RD_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID4RD_PAGE register field value. */
#define ALT_ACPIDMAP_VID4RD_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID4RD_PAGE register field value. */
#define ALT_ACPIDMAP_VID4RD_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID4RD_PAGE register field. */
#define ALT_ACPIDMAP_VID4RD_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4RD_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID4RD_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID4RD_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4RD_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4RD_MID register field. */
#define ALT_ACPIDMAP_VID4RD_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4RD_MID register field. */
#define ALT_ACPIDMAP_VID4RD_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID4RD_MID register field. */
#define ALT_ACPIDMAP_VID4RD_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID4RD_MID register field value. */
#define ALT_ACPIDMAP_VID4RD_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID4RD_MID register field value. */
#define ALT_ACPIDMAP_VID4RD_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID4RD_MID register field. */
#define ALT_ACPIDMAP_VID4RD_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4RD_MID field value from a register. */
#define ALT_ACPIDMAP_VID4RD_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID4RD_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4RD_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4RD_FORCE register field. */
#define ALT_ACPIDMAP_VID4RD_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4RD_FORCE register field. */
#define ALT_ACPIDMAP_VID4RD_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID4RD_FORCE register field. */
#define ALT_ACPIDMAP_VID4RD_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID4RD_FORCE register field value. */
#define ALT_ACPIDMAP_VID4RD_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID4RD_FORCE register field value. */
#define ALT_ACPIDMAP_VID4RD_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID4RD_FORCE register field. */
#define ALT_ACPIDMAP_VID4RD_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4RD_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID4RD_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID4RD_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4RD_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID4RD.
 */
struct ALT_ACPIDMAP_VID4RD_s
{
    uint32_t        :  4;  /* *UNDEFINED* */
    uint32_t  user  :  5;  /* ARUSER value to SCU */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  page  :  2;  /* ARADDR 1GB Page Decoder */
    uint32_t        :  2;  /* *UNDEFINED* */
    uint32_t  mid   : 12;  /* Remap Master ID */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  force :  1;  /* Force Mapping */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID4RD. */
typedef volatile struct ALT_ACPIDMAP_VID4RD_s  ALT_ACPIDMAP_VID4RD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID4RD register from the beginning of the component. */
#define ALT_ACPIDMAP_VID4RD_OFST        0x10

/*
 * Register : Write AXI Master Mapping Register for Fixed Virtual ID 4 - vid4wr
 * 
 * The Write AXI Master Mapping Register contains the USER, ADDR page, and ID
 * signals mapping values for particular transaction with 12-bit ID which locks the
 * fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description            
 * :--------|:-------|:------|:------------------------
 *  [3:0]   | ???    | 0x0   | *UNDEFINED*            
 *  [8:4]   | RW     | 0x0   | AWUSER value to SCU    
 *  [11:9]  | ???    | 0x0   | *UNDEFINED*            
 *  [13:12] | RW     | 0x0   | AWADDR 1GB Page Decoder
 *  [15:14] | ???    | 0x0   | *UNDEFINED*            
 *  [27:16] | RW     | 0x0   | Remap Master ID        
 *  [30:28] | ???    | 0x0   | *UNDEFINED*            
 *  [31]    | RW     | 0x0   | Force Mapping          
 * 
 */
/*
 * Field : AWUSER value to SCU - user
 * 
 * This value is propagated to SCU as AWUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4WR_USER register field. */
#define ALT_ACPIDMAP_VID4WR_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4WR_USER register field. */
#define ALT_ACPIDMAP_VID4WR_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID4WR_USER register field. */
#define ALT_ACPIDMAP_VID4WR_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID4WR_USER register field value. */
#define ALT_ACPIDMAP_VID4WR_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID4WR_USER register field value. */
#define ALT_ACPIDMAP_VID4WR_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID4WR_USER register field. */
#define ALT_ACPIDMAP_VID4WR_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4WR_USER field value from a register. */
#define ALT_ACPIDMAP_VID4WR_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID4WR_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4WR_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : AWADDR 1GB Page Decoder - page
 * 
 * AWADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4WR_PAGE register field. */
#define ALT_ACPIDMAP_VID4WR_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4WR_PAGE register field. */
#define ALT_ACPIDMAP_VID4WR_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID4WR_PAGE register field. */
#define ALT_ACPIDMAP_VID4WR_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID4WR_PAGE register field value. */
#define ALT_ACPIDMAP_VID4WR_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID4WR_PAGE register field value. */
#define ALT_ACPIDMAP_VID4WR_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID4WR_PAGE register field. */
#define ALT_ACPIDMAP_VID4WR_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4WR_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID4WR_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID4WR_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4WR_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4WR_MID register field. */
#define ALT_ACPIDMAP_VID4WR_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4WR_MID register field. */
#define ALT_ACPIDMAP_VID4WR_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID4WR_MID register field. */
#define ALT_ACPIDMAP_VID4WR_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID4WR_MID register field value. */
#define ALT_ACPIDMAP_VID4WR_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID4WR_MID register field value. */
#define ALT_ACPIDMAP_VID4WR_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID4WR_MID register field. */
#define ALT_ACPIDMAP_VID4WR_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4WR_MID field value from a register. */
#define ALT_ACPIDMAP_VID4WR_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID4WR_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4WR_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4WR_FORCE register field. */
#define ALT_ACPIDMAP_VID4WR_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4WR_FORCE register field. */
#define ALT_ACPIDMAP_VID4WR_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID4WR_FORCE register field. */
#define ALT_ACPIDMAP_VID4WR_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID4WR_FORCE register field value. */
#define ALT_ACPIDMAP_VID4WR_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID4WR_FORCE register field value. */
#define ALT_ACPIDMAP_VID4WR_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID4WR_FORCE register field. */
#define ALT_ACPIDMAP_VID4WR_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4WR_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID4WR_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID4WR_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4WR_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID4WR.
 */
struct ALT_ACPIDMAP_VID4WR_s
{
    uint32_t        :  4;  /* *UNDEFINED* */
    uint32_t  user  :  5;  /* AWUSER value to SCU */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  page  :  2;  /* AWADDR 1GB Page Decoder */
    uint32_t        :  2;  /* *UNDEFINED* */
    uint32_t  mid   : 12;  /* Remap Master ID */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  force :  1;  /* Force Mapping */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID4WR. */
typedef volatile struct ALT_ACPIDMAP_VID4WR_s  ALT_ACPIDMAP_VID4WR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID4WR register from the beginning of the component. */
#define ALT_ACPIDMAP_VID4WR_OFST        0x14

/*
 * Register : Read AXI Master Mapping Register for Fixed Virtual ID 5 - vid5rd
 * 
 * The Read AXI Master Mapping Register contains the USER, ADDR page, and ID
 * signals mapping values for particular transaction with 12-bit ID which locks the
 * fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description            
 * :--------|:-------|:------|:------------------------
 *  [3:0]   | ???    | 0x0   | *UNDEFINED*            
 *  [8:4]   | RW     | 0x0   | ARUSER value to SCU    
 *  [11:9]  | ???    | 0x0   | *UNDEFINED*            
 *  [13:12] | RW     | 0x0   | ARADDR 1GB Page Decoder
 *  [15:14] | ???    | 0x0   | *UNDEFINED*            
 *  [27:16] | RW     | 0x0   | Remap Master ID        
 *  [30:28] | ???    | 0x0   | *UNDEFINED*            
 *  [31]    | RW     | 0x0   | Force Mapping          
 * 
 */
/*
 * Field : ARUSER value to SCU - user
 * 
 * This value is propagated to SCU as ARUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5RD_USER register field. */
#define ALT_ACPIDMAP_VID5RD_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5RD_USER register field. */
#define ALT_ACPIDMAP_VID5RD_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID5RD_USER register field. */
#define ALT_ACPIDMAP_VID5RD_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID5RD_USER register field value. */
#define ALT_ACPIDMAP_VID5RD_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID5RD_USER register field value. */
#define ALT_ACPIDMAP_VID5RD_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID5RD_USER register field. */
#define ALT_ACPIDMAP_VID5RD_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5RD_USER field value from a register. */
#define ALT_ACPIDMAP_VID5RD_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID5RD_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5RD_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : ARADDR 1GB Page Decoder - page
 * 
 * ARADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5RD_PAGE register field. */
#define ALT_ACPIDMAP_VID5RD_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5RD_PAGE register field. */
#define ALT_ACPIDMAP_VID5RD_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID5RD_PAGE register field. */
#define ALT_ACPIDMAP_VID5RD_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID5RD_PAGE register field value. */
#define ALT_ACPIDMAP_VID5RD_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID5RD_PAGE register field value. */
#define ALT_ACPIDMAP_VID5RD_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID5RD_PAGE register field. */
#define ALT_ACPIDMAP_VID5RD_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5RD_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID5RD_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID5RD_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5RD_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5RD_MID register field. */
#define ALT_ACPIDMAP_VID5RD_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5RD_MID register field. */
#define ALT_ACPIDMAP_VID5RD_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID5RD_MID register field. */
#define ALT_ACPIDMAP_VID5RD_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID5RD_MID register field value. */
#define ALT_ACPIDMAP_VID5RD_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID5RD_MID register field value. */
#define ALT_ACPIDMAP_VID5RD_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID5RD_MID register field. */
#define ALT_ACPIDMAP_VID5RD_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5RD_MID field value from a register. */
#define ALT_ACPIDMAP_VID5RD_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID5RD_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5RD_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5RD_FORCE register field. */
#define ALT_ACPIDMAP_VID5RD_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5RD_FORCE register field. */
#define ALT_ACPIDMAP_VID5RD_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID5RD_FORCE register field. */
#define ALT_ACPIDMAP_VID5RD_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID5RD_FORCE register field value. */
#define ALT_ACPIDMAP_VID5RD_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID5RD_FORCE register field value. */
#define ALT_ACPIDMAP_VID5RD_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID5RD_FORCE register field. */
#define ALT_ACPIDMAP_VID5RD_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5RD_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID5RD_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID5RD_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5RD_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID5RD.
 */
struct ALT_ACPIDMAP_VID5RD_s
{
    uint32_t        :  4;  /* *UNDEFINED* */
    uint32_t  user  :  5;  /* ARUSER value to SCU */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  page  :  2;  /* ARADDR 1GB Page Decoder */
    uint32_t        :  2;  /* *UNDEFINED* */
    uint32_t  mid   : 12;  /* Remap Master ID */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  force :  1;  /* Force Mapping */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID5RD. */
typedef volatile struct ALT_ACPIDMAP_VID5RD_s  ALT_ACPIDMAP_VID5RD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID5RD register from the beginning of the component. */
#define ALT_ACPIDMAP_VID5RD_OFST        0x18

/*
 * Register : Write AXI Master Mapping Register for Fixed Virtual ID 5 - vid5wr
 * 
 * The Write AXI Master Mapping Register contains the USER, ADDR page, and ID
 * signals mapping values for particular transaction with 12-bit ID which locks the
 * fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description            
 * :--------|:-------|:------|:------------------------
 *  [3:0]   | ???    | 0x0   | *UNDEFINED*            
 *  [8:4]   | RW     | 0x0   | AWUSER value to SCU    
 *  [11:9]  | ???    | 0x0   | *UNDEFINED*            
 *  [13:12] | RW     | 0x0   | AWADDR 1GB Page Decoder
 *  [15:14] | ???    | 0x0   | *UNDEFINED*            
 *  [27:16] | RW     | 0x0   | Remap Master ID        
 *  [30:28] | ???    | 0x0   | *UNDEFINED*            
 *  [31]    | RW     | 0x0   | Force Mapping          
 * 
 */
/*
 * Field : AWUSER value to SCU - user
 * 
 * This value is propagated to SCU as AWUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5WR_USER register field. */
#define ALT_ACPIDMAP_VID5WR_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5WR_USER register field. */
#define ALT_ACPIDMAP_VID5WR_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID5WR_USER register field. */
#define ALT_ACPIDMAP_VID5WR_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID5WR_USER register field value. */
#define ALT_ACPIDMAP_VID5WR_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID5WR_USER register field value. */
#define ALT_ACPIDMAP_VID5WR_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID5WR_USER register field. */
#define ALT_ACPIDMAP_VID5WR_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5WR_USER field value from a register. */
#define ALT_ACPIDMAP_VID5WR_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID5WR_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5WR_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : AWADDR 1GB Page Decoder - page
 * 
 * AWADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5WR_PAGE register field. */
#define ALT_ACPIDMAP_VID5WR_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5WR_PAGE register field. */
#define ALT_ACPIDMAP_VID5WR_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID5WR_PAGE register field. */
#define ALT_ACPIDMAP_VID5WR_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID5WR_PAGE register field value. */
#define ALT_ACPIDMAP_VID5WR_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID5WR_PAGE register field value. */
#define ALT_ACPIDMAP_VID5WR_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID5WR_PAGE register field. */
#define ALT_ACPIDMAP_VID5WR_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5WR_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID5WR_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID5WR_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5WR_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5WR_MID register field. */
#define ALT_ACPIDMAP_VID5WR_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5WR_MID register field. */
#define ALT_ACPIDMAP_VID5WR_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID5WR_MID register field. */
#define ALT_ACPIDMAP_VID5WR_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID5WR_MID register field value. */
#define ALT_ACPIDMAP_VID5WR_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID5WR_MID register field value. */
#define ALT_ACPIDMAP_VID5WR_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID5WR_MID register field. */
#define ALT_ACPIDMAP_VID5WR_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5WR_MID field value from a register. */
#define ALT_ACPIDMAP_VID5WR_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID5WR_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5WR_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5WR_FORCE register field. */
#define ALT_ACPIDMAP_VID5WR_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5WR_FORCE register field. */
#define ALT_ACPIDMAP_VID5WR_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID5WR_FORCE register field. */
#define ALT_ACPIDMAP_VID5WR_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID5WR_FORCE register field value. */
#define ALT_ACPIDMAP_VID5WR_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID5WR_FORCE register field value. */
#define ALT_ACPIDMAP_VID5WR_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID5WR_FORCE register field. */
#define ALT_ACPIDMAP_VID5WR_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5WR_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID5WR_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID5WR_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5WR_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID5WR.
 */
struct ALT_ACPIDMAP_VID5WR_s
{
    uint32_t        :  4;  /* *UNDEFINED* */
    uint32_t  user  :  5;  /* AWUSER value to SCU */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  page  :  2;  /* AWADDR 1GB Page Decoder */
    uint32_t        :  2;  /* *UNDEFINED* */
    uint32_t  mid   : 12;  /* Remap Master ID */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  force :  1;  /* Force Mapping */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID5WR. */
typedef volatile struct ALT_ACPIDMAP_VID5WR_s  ALT_ACPIDMAP_VID5WR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID5WR register from the beginning of the component. */
#define ALT_ACPIDMAP_VID5WR_OFST        0x1c

/*
 * Register : Read AXI Master Mapping Register for Fixed Virtual ID 6 - vid6rd
 * 
 * The Read AXI Master Mapping Register contains the USER, ADDR page, and ID
 * signals mapping values for particular transaction with 12-bit ID which locks the
 * fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description            
 * :--------|:-------|:------|:------------------------
 *  [3:0]   | ???    | 0x0   | *UNDEFINED*            
 *  [8:4]   | RW     | 0x0   | ARUSER value to SCU    
 *  [11:9]  | ???    | 0x0   | *UNDEFINED*            
 *  [13:12] | RW     | 0x0   | ARADDR 1GB Page Decoder
 *  [15:14] | ???    | 0x0   | *UNDEFINED*            
 *  [27:16] | RW     | 0x0   | Remap Master ID        
 *  [30:28] | ???    | 0x0   | *UNDEFINED*            
 *  [31]    | RW     | 0x0   | Force Mapping          
 * 
 */
/*
 * Field : ARUSER value to SCU - user
 * 
 * This value is propagated to SCU as ARUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6RD_USER register field. */
#define ALT_ACPIDMAP_VID6RD_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6RD_USER register field. */
#define ALT_ACPIDMAP_VID6RD_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID6RD_USER register field. */
#define ALT_ACPIDMAP_VID6RD_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID6RD_USER register field value. */
#define ALT_ACPIDMAP_VID6RD_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID6RD_USER register field value. */
#define ALT_ACPIDMAP_VID6RD_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID6RD_USER register field. */
#define ALT_ACPIDMAP_VID6RD_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6RD_USER field value from a register. */
#define ALT_ACPIDMAP_VID6RD_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID6RD_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6RD_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : ARADDR 1GB Page Decoder - page
 * 
 * ARADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6RD_PAGE register field. */
#define ALT_ACPIDMAP_VID6RD_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6RD_PAGE register field. */
#define ALT_ACPIDMAP_VID6RD_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID6RD_PAGE register field. */
#define ALT_ACPIDMAP_VID6RD_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID6RD_PAGE register field value. */
#define ALT_ACPIDMAP_VID6RD_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID6RD_PAGE register field value. */
#define ALT_ACPIDMAP_VID6RD_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID6RD_PAGE register field. */
#define ALT_ACPIDMAP_VID6RD_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6RD_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID6RD_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID6RD_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6RD_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6RD_MID register field. */
#define ALT_ACPIDMAP_VID6RD_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6RD_MID register field. */
#define ALT_ACPIDMAP_VID6RD_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID6RD_MID register field. */
#define ALT_ACPIDMAP_VID6RD_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID6RD_MID register field value. */
#define ALT_ACPIDMAP_VID6RD_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID6RD_MID register field value. */
#define ALT_ACPIDMAP_VID6RD_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID6RD_MID register field. */
#define ALT_ACPIDMAP_VID6RD_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6RD_MID field value from a register. */
#define ALT_ACPIDMAP_VID6RD_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID6RD_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6RD_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6RD_FORCE register field. */
#define ALT_ACPIDMAP_VID6RD_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6RD_FORCE register field. */
#define ALT_ACPIDMAP_VID6RD_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID6RD_FORCE register field. */
#define ALT_ACPIDMAP_VID6RD_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID6RD_FORCE register field value. */
#define ALT_ACPIDMAP_VID6RD_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID6RD_FORCE register field value. */
#define ALT_ACPIDMAP_VID6RD_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID6RD_FORCE register field. */
#define ALT_ACPIDMAP_VID6RD_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6RD_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID6RD_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID6RD_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6RD_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID6RD.
 */
struct ALT_ACPIDMAP_VID6RD_s
{
    uint32_t        :  4;  /* *UNDEFINED* */
    uint32_t  user  :  5;  /* ARUSER value to SCU */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  page  :  2;  /* ARADDR 1GB Page Decoder */
    uint32_t        :  2;  /* *UNDEFINED* */
    uint32_t  mid   : 12;  /* Remap Master ID */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  force :  1;  /* Force Mapping */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID6RD. */
typedef volatile struct ALT_ACPIDMAP_VID6RD_s  ALT_ACPIDMAP_VID6RD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID6RD register from the beginning of the component. */
#define ALT_ACPIDMAP_VID6RD_OFST        0x20

/*
 * Register : Write AXI Master Mapping Register for Fixed Virtual ID 6 - vid6wr
 * 
 * The Write AXI Master Mapping Register contains the USER, ADDR page, and ID
 * signals mapping values for particular transaction with 12-bit ID which locks the
 * fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description            
 * :--------|:-------|:------|:------------------------
 *  [3:0]   | ???    | 0x0   | *UNDEFINED*            
 *  [8:4]   | RW     | 0x0   | AWUSER value to SCU    
 *  [11:9]  | ???    | 0x0   | *UNDEFINED*            
 *  [13:12] | RW     | 0x0   | AWADDR 1GB Page Decoder
 *  [15:14] | ???    | 0x0   | *UNDEFINED*            
 *  [27:16] | RW     | 0x0   | Remap Master ID        
 *  [30:28] | ???    | 0x0   | *UNDEFINED*            
 *  [31]    | RW     | 0x0   | Force Mapping          
 * 
 */
/*
 * Field : AWUSER value to SCU - user
 * 
 * This value is propagated to SCU as AWUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6WR_USER register field. */
#define ALT_ACPIDMAP_VID6WR_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6WR_USER register field. */
#define ALT_ACPIDMAP_VID6WR_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID6WR_USER register field. */
#define ALT_ACPIDMAP_VID6WR_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID6WR_USER register field value. */
#define ALT_ACPIDMAP_VID6WR_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID6WR_USER register field value. */
#define ALT_ACPIDMAP_VID6WR_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID6WR_USER register field. */
#define ALT_ACPIDMAP_VID6WR_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6WR_USER field value from a register. */
#define ALT_ACPIDMAP_VID6WR_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID6WR_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6WR_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : AWADDR 1GB Page Decoder - page
 * 
 * AWADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6WR_PAGE register field. */
#define ALT_ACPIDMAP_VID6WR_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6WR_PAGE register field. */
#define ALT_ACPIDMAP_VID6WR_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID6WR_PAGE register field. */
#define ALT_ACPIDMAP_VID6WR_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID6WR_PAGE register field value. */
#define ALT_ACPIDMAP_VID6WR_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID6WR_PAGE register field value. */
#define ALT_ACPIDMAP_VID6WR_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID6WR_PAGE register field. */
#define ALT_ACPIDMAP_VID6WR_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6WR_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID6WR_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID6WR_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6WR_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6WR_MID register field. */
#define ALT_ACPIDMAP_VID6WR_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6WR_MID register field. */
#define ALT_ACPIDMAP_VID6WR_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID6WR_MID register field. */
#define ALT_ACPIDMAP_VID6WR_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID6WR_MID register field value. */
#define ALT_ACPIDMAP_VID6WR_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID6WR_MID register field value. */
#define ALT_ACPIDMAP_VID6WR_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID6WR_MID register field. */
#define ALT_ACPIDMAP_VID6WR_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6WR_MID field value from a register. */
#define ALT_ACPIDMAP_VID6WR_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID6WR_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6WR_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6WR_FORCE register field. */
#define ALT_ACPIDMAP_VID6WR_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6WR_FORCE register field. */
#define ALT_ACPIDMAP_VID6WR_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID6WR_FORCE register field. */
#define ALT_ACPIDMAP_VID6WR_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID6WR_FORCE register field value. */
#define ALT_ACPIDMAP_VID6WR_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID6WR_FORCE register field value. */
#define ALT_ACPIDMAP_VID6WR_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID6WR_FORCE register field. */
#define ALT_ACPIDMAP_VID6WR_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6WR_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID6WR_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID6WR_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6WR_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID6WR.
 */
struct ALT_ACPIDMAP_VID6WR_s
{
    uint32_t        :  4;  /* *UNDEFINED* */
    uint32_t  user  :  5;  /* AWUSER value to SCU */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  page  :  2;  /* AWADDR 1GB Page Decoder */
    uint32_t        :  2;  /* *UNDEFINED* */
    uint32_t  mid   : 12;  /* Remap Master ID */
    uint32_t        :  3;  /* *UNDEFINED* */
    uint32_t  force :  1;  /* Force Mapping */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID6WR. */
typedef volatile struct ALT_ACPIDMAP_VID6WR_s  ALT_ACPIDMAP_VID6WR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID6WR register from the beginning of the component. */
#define ALT_ACPIDMAP_VID6WR_OFST        0x24

/*
 * Register : Read AXI Master Mapping Register for Dynamic Virtual ID Remap - dynrd
 * 
 * The Read AXI Master Mapping Register contains the USER, and ADDR page signals
 * mapping values for transaction that dynamically remapped to one of the available
 * 3-bit virtual IDs.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description            
 * :--------|:-------|:------|:------------------------
 *  [3:0]   | ???    | 0x0   | *UNDEFINED*            
 *  [8:4]   | RW     | 0x0   | ARUSER value to SCU    
 *  [11:9]  | ???    | 0x0   | *UNDEFINED*            
 *  [13:12] | RW     | 0x0   | ARADDR 1GB Page Decoder
 *  [31:14] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : ARUSER value to SCU - user
 * 
 * This value is propagated to SCU as ARUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_DYNRD_USER register field. */
#define ALT_ACPIDMAP_DYNRD_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_DYNRD_USER register field. */
#define ALT_ACPIDMAP_DYNRD_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_DYNRD_USER register field. */
#define ALT_ACPIDMAP_DYNRD_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_DYNRD_USER register field value. */
#define ALT_ACPIDMAP_DYNRD_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_DYNRD_USER register field value. */
#define ALT_ACPIDMAP_DYNRD_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_DYNRD_USER register field. */
#define ALT_ACPIDMAP_DYNRD_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_DYNRD_USER field value from a register. */
#define ALT_ACPIDMAP_DYNRD_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_DYNRD_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_DYNRD_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : ARADDR 1GB Page Decoder - page
 * 
 * ARADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_DYNRD_PAGE register field. */
#define ALT_ACPIDMAP_DYNRD_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_DYNRD_PAGE register field. */
#define ALT_ACPIDMAP_DYNRD_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_DYNRD_PAGE register field. */
#define ALT_ACPIDMAP_DYNRD_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_DYNRD_PAGE register field value. */
#define ALT_ACPIDMAP_DYNRD_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_DYNRD_PAGE register field value. */
#define ALT_ACPIDMAP_DYNRD_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_DYNRD_PAGE register field. */
#define ALT_ACPIDMAP_DYNRD_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_DYNRD_PAGE field value from a register. */
#define ALT_ACPIDMAP_DYNRD_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_DYNRD_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_DYNRD_PAGE_SET(value) (((value) << 12) & 0x00003000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_DYNRD.
 */
struct ALT_ACPIDMAP_DYNRD_s
{
    uint32_t       :  4;  /* *UNDEFINED* */
    uint32_t  user :  5;  /* ARUSER value to SCU */
    uint32_t       :  3;  /* *UNDEFINED* */
    uint32_t  page :  2;  /* ARADDR 1GB Page Decoder */
    uint32_t       : 18;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_ACPIDMAP_DYNRD. */
typedef volatile struct ALT_ACPIDMAP_DYNRD_s  ALT_ACPIDMAP_DYNRD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_DYNRD register from the beginning of the component. */
#define ALT_ACPIDMAP_DYNRD_OFST        0x28

/*
 * Register : Write AXI Master Mapping Register for Dynamic Virtual ID Remap - dynwr
 * 
 * The Write AXI Master Mapping Register contains the USER, and ADDR page signals
 * mapping values for transaction that dynamically remapped to one of the available
 * 3-bit virtual IDs.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description            
 * :--------|:-------|:------|:------------------------
 *  [3:0]   | ???    | 0x0   | *UNDEFINED*            
 *  [8:4]   | RW     | 0x0   | AWUSER value to SCU    
 *  [11:9]  | ???    | 0x0   | *UNDEFINED*            
 *  [13:12] | RW     | 0x0   | AWADDR 1GB Page Decoder
 *  [31:14] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : AWUSER value to SCU - user
 * 
 * This value is propagated to SCU as AWUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_DYNWR_USER register field. */
#define ALT_ACPIDMAP_DYNWR_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_DYNWR_USER register field. */
#define ALT_ACPIDMAP_DYNWR_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_DYNWR_USER register field. */
#define ALT_ACPIDMAP_DYNWR_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_DYNWR_USER register field value. */
#define ALT_ACPIDMAP_DYNWR_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_DYNWR_USER register field value. */
#define ALT_ACPIDMAP_DYNWR_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_DYNWR_USER register field. */
#define ALT_ACPIDMAP_DYNWR_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_DYNWR_USER field value from a register. */
#define ALT_ACPIDMAP_DYNWR_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_DYNWR_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_DYNWR_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : AWADDR 1GB Page Decoder - page
 * 
 * AWADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_DYNWR_PAGE register field. */
#define ALT_ACPIDMAP_DYNWR_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_DYNWR_PAGE register field. */
#define ALT_ACPIDMAP_DYNWR_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_DYNWR_PAGE register field. */
#define ALT_ACPIDMAP_DYNWR_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_DYNWR_PAGE register field value. */
#define ALT_ACPIDMAP_DYNWR_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_DYNWR_PAGE register field value. */
#define ALT_ACPIDMAP_DYNWR_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_DYNWR_PAGE register field. */
#define ALT_ACPIDMAP_DYNWR_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_DYNWR_PAGE field value from a register. */
#define ALT_ACPIDMAP_DYNWR_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_DYNWR_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_DYNWR_PAGE_SET(value) (((value) << 12) & 0x00003000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_DYNWR.
 */
struct ALT_ACPIDMAP_DYNWR_s
{
    uint32_t       :  4;  /* *UNDEFINED* */
    uint32_t  user :  5;  /* AWUSER value to SCU */
    uint32_t       :  3;  /* *UNDEFINED* */
    uint32_t  page :  2;  /* AWADDR 1GB Page Decoder */
    uint32_t       : 18;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_ACPIDMAP_DYNWR. */
typedef volatile struct ALT_ACPIDMAP_DYNWR_s  ALT_ACPIDMAP_DYNWR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_DYNWR register from the beginning of the component. */
#define ALT_ACPIDMAP_DYNWR_OFST        0x2c

/*
 * Register : Read AXI Master Mapping Status Register for Fixed Virtual ID 2 - vid2rd_s
 * 
 * The Read AXI Master Mapping Status Register contains the configured USER, ADDR
 * page, and ID signals mapping values for particular transaction with 12-bit ID
 * which locks the fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                          
 * :--------|:-------|:--------|:--------------------------------------
 *  [3:0]   | ???    | 0x0     | *UNDEFINED*                          
 *  [8:4]   | R      | 0x1     | ARUSER value to SCU for ID=2 (Status)
 *  [11:9]  | ???    | 0x0     | *UNDEFINED*                          
 *  [13:12] | R      | Unknown | ARADDR 1GB Page Decoder (Status)     
 *  [15:14] | ???    | 0x0     | *UNDEFINED*                          
 *  [27:16] | R      | 0x4     | Remap Master ID = DAP ID (Status)    
 *  [30:28] | ???    | 0x0     | *UNDEFINED*                          
 *  [31]    | R      | 0x1     | Force Mapping for ID=2 (Status)      
 * 
 */
/*
 * Field : ARUSER value to SCU for ID=2 (Status) - user
 * 
 * This value is propagated to SCU as ARUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2RD_S_USER register field. */
#define ALT_ACPIDMAP_VID2RD_S_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2RD_S_USER register field. */
#define ALT_ACPIDMAP_VID2RD_S_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID2RD_S_USER register field. */
#define ALT_ACPIDMAP_VID2RD_S_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID2RD_S_USER register field value. */
#define ALT_ACPIDMAP_VID2RD_S_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID2RD_S_USER register field value. */
#define ALT_ACPIDMAP_VID2RD_S_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID2RD_S_USER register field. */
#define ALT_ACPIDMAP_VID2RD_S_USER_RESET      0x1
/* Extracts the ALT_ACPIDMAP_VID2RD_S_USER field value from a register. */
#define ALT_ACPIDMAP_VID2RD_S_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID2RD_S_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2RD_S_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : ARADDR 1GB Page Decoder (Status) - page
 * 
 * ARADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID2RD_S_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID2RD_S_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID2RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID2RD_S_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID2RD_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID2RD_S_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID2RD_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID2RD_S_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID2RD_S_PAGE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID2RD_S_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID2RD_S_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID2RD_S_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID2RD_S_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2RD_S_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID = DAP ID (Status) - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2RD_S_MID register field. */
#define ALT_ACPIDMAP_VID2RD_S_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2RD_S_MID register field. */
#define ALT_ACPIDMAP_VID2RD_S_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID2RD_S_MID register field. */
#define ALT_ACPIDMAP_VID2RD_S_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID2RD_S_MID register field value. */
#define ALT_ACPIDMAP_VID2RD_S_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID2RD_S_MID register field value. */
#define ALT_ACPIDMAP_VID2RD_S_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID2RD_S_MID register field. */
#define ALT_ACPIDMAP_VID2RD_S_MID_RESET      0x4
/* Extracts the ALT_ACPIDMAP_VID2RD_S_MID field value from a register. */
#define ALT_ACPIDMAP_VID2RD_S_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID2RD_S_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2RD_S_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping for ID=2 (Status) - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID2RD_S_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID2RD_S_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID2RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID2RD_S_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID2RD_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID2RD_S_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID2RD_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID2RD_S_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID2RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID2RD_S_FORCE_RESET      0x1
/* Extracts the ALT_ACPIDMAP_VID2RD_S_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID2RD_S_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID2RD_S_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2RD_S_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID2RD_S.
 */
struct ALT_ACPIDMAP_VID2RD_S_s
{
    uint32_t              :  4;  /* *UNDEFINED* */
    const uint32_t  user  :  5;  /* ARUSER value to SCU for ID=2 (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  page  :  2;  /* ARADDR 1GB Page Decoder (Status) */
    uint32_t              :  2;  /* *UNDEFINED* */
    const uint32_t  mid   : 12;  /* Remap Master ID = DAP ID (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  force :  1;  /* Force Mapping for ID=2 (Status) */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID2RD_S. */
typedef volatile struct ALT_ACPIDMAP_VID2RD_S_s  ALT_ACPIDMAP_VID2RD_S_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID2RD_S register from the beginning of the component. */
#define ALT_ACPIDMAP_VID2RD_S_OFST        0x30

/*
 * Register : Write AXI Master Mapping Status Register for Fixed Virtual ID 2 - vid2wr_s
 * 
 * The Write AXI Master Mapping Status Register contains the configured USER, ADDR
 * page, and ID signals mapping values for particular transaction with 12-bit ID
 * which locks the fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                          
 * :--------|:-------|:--------|:--------------------------------------
 *  [3:0]   | ???    | 0x0     | *UNDEFINED*                          
 *  [8:4]   | R      | 0x1     | AWUSER value to SCU for ID=2 (Status)
 *  [11:9]  | ???    | 0x0     | *UNDEFINED*                          
 *  [13:12] | R      | Unknown | AWADDR 1GB Page Decoder (Status)     
 *  [15:14] | ???    | 0x0     | *UNDEFINED*                          
 *  [27:16] | R      | 0x4     | Remap Master ID = DAP ID (Status)    
 *  [30:28] | ???    | 0x0     | *UNDEFINED*                          
 *  [31]    | R      | 0x1     | Force Mapping for ID=2 (Status)      
 * 
 */
/*
 * Field : AWUSER value to SCU for ID=2 (Status) - user
 * 
 * This value is propagated to SCU as AWUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2WR_S_USER register field. */
#define ALT_ACPIDMAP_VID2WR_S_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2WR_S_USER register field. */
#define ALT_ACPIDMAP_VID2WR_S_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID2WR_S_USER register field. */
#define ALT_ACPIDMAP_VID2WR_S_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID2WR_S_USER register field value. */
#define ALT_ACPIDMAP_VID2WR_S_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID2WR_S_USER register field value. */
#define ALT_ACPIDMAP_VID2WR_S_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID2WR_S_USER register field. */
#define ALT_ACPIDMAP_VID2WR_S_USER_RESET      0x1
/* Extracts the ALT_ACPIDMAP_VID2WR_S_USER field value from a register. */
#define ALT_ACPIDMAP_VID2WR_S_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID2WR_S_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2WR_S_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : AWADDR 1GB Page Decoder (Status) - page
 * 
 * AWADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID2WR_S_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID2WR_S_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID2WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID2WR_S_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID2WR_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID2WR_S_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID2WR_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID2WR_S_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID2WR_S_PAGE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID2WR_S_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID2WR_S_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID2WR_S_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID2WR_S_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2WR_S_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID = DAP ID (Status) - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2WR_S_MID register field. */
#define ALT_ACPIDMAP_VID2WR_S_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2WR_S_MID register field. */
#define ALT_ACPIDMAP_VID2WR_S_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID2WR_S_MID register field. */
#define ALT_ACPIDMAP_VID2WR_S_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID2WR_S_MID register field value. */
#define ALT_ACPIDMAP_VID2WR_S_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID2WR_S_MID register field value. */
#define ALT_ACPIDMAP_VID2WR_S_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID2WR_S_MID register field. */
#define ALT_ACPIDMAP_VID2WR_S_MID_RESET      0x4
/* Extracts the ALT_ACPIDMAP_VID2WR_S_MID field value from a register. */
#define ALT_ACPIDMAP_VID2WR_S_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID2WR_S_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2WR_S_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping for ID=2 (Status) - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID2WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID2WR_S_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID2WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID2WR_S_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID2WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID2WR_S_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID2WR_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID2WR_S_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID2WR_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID2WR_S_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID2WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID2WR_S_FORCE_RESET      0x1
/* Extracts the ALT_ACPIDMAP_VID2WR_S_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID2WR_S_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID2WR_S_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID2WR_S_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID2WR_S.
 */
struct ALT_ACPIDMAP_VID2WR_S_s
{
    uint32_t              :  4;  /* *UNDEFINED* */
    const uint32_t  user  :  5;  /* AWUSER value to SCU for ID=2 (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  page  :  2;  /* AWADDR 1GB Page Decoder (Status) */
    uint32_t              :  2;  /* *UNDEFINED* */
    const uint32_t  mid   : 12;  /* Remap Master ID = DAP ID (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  force :  1;  /* Force Mapping for ID=2 (Status) */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID2WR_S. */
typedef volatile struct ALT_ACPIDMAP_VID2WR_S_s  ALT_ACPIDMAP_VID2WR_S_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID2WR_S register from the beginning of the component. */
#define ALT_ACPIDMAP_VID2WR_S_OFST        0x34

/*
 * Register : Read AXI Master Mapping Status Register for Fixed Virtual ID 3 - vid3rd_s
 * 
 * The Read AXI Master Mapping Status Register contains the configured USER, ADDR
 * page, and ID signals mapping values for particular transaction with 12-bit ID
 * which locks the fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                     
 * :--------|:-------|:--------|:---------------------------------
 *  [3:0]   | ???    | 0x0     | *UNDEFINED*                     
 *  [8:4]   | R      | Unknown | ARUSER value to SCU (Status)    
 *  [11:9]  | ???    | 0x0     | *UNDEFINED*                     
 *  [13:12] | R      | Unknown | ARADDR 1GB Page Decoder (Status)
 *  [15:14] | ???    | 0x0     | *UNDEFINED*                     
 *  [27:16] | R      | Unknown | Remap Master ID (Status)        
 *  [30:28] | ???    | 0x0     | *UNDEFINED*                     
 *  [31]    | R      | Unknown | Force Mapping (Status)          
 * 
 */
/*
 * Field : ARUSER value to SCU (Status) - user
 * 
 * This value is propagated to SCU as ARUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3RD_S_USER register field. */
#define ALT_ACPIDMAP_VID3RD_S_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3RD_S_USER register field. */
#define ALT_ACPIDMAP_VID3RD_S_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID3RD_S_USER register field. */
#define ALT_ACPIDMAP_VID3RD_S_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID3RD_S_USER register field value. */
#define ALT_ACPIDMAP_VID3RD_S_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID3RD_S_USER register field value. */
#define ALT_ACPIDMAP_VID3RD_S_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID3RD_S_USER register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID3RD_S_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3RD_S_USER field value from a register. */
#define ALT_ACPIDMAP_VID3RD_S_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID3RD_S_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3RD_S_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : ARADDR 1GB Page Decoder (Status) - page
 * 
 * ARADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID3RD_S_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID3RD_S_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID3RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID3RD_S_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID3RD_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID3RD_S_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID3RD_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID3RD_S_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID3RD_S_PAGE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID3RD_S_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3RD_S_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID3RD_S_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID3RD_S_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3RD_S_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID (Status) - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3RD_S_MID register field. */
#define ALT_ACPIDMAP_VID3RD_S_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3RD_S_MID register field. */
#define ALT_ACPIDMAP_VID3RD_S_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID3RD_S_MID register field. */
#define ALT_ACPIDMAP_VID3RD_S_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID3RD_S_MID register field value. */
#define ALT_ACPIDMAP_VID3RD_S_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID3RD_S_MID register field value. */
#define ALT_ACPIDMAP_VID3RD_S_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID3RD_S_MID register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID3RD_S_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3RD_S_MID field value from a register. */
#define ALT_ACPIDMAP_VID3RD_S_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID3RD_S_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3RD_S_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping (Status) - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID3RD_S_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID3RD_S_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID3RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID3RD_S_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID3RD_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID3RD_S_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID3RD_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID3RD_S_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID3RD_S_FORCE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID3RD_S_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3RD_S_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID3RD_S_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID3RD_S_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3RD_S_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID3RD_S.
 */
struct ALT_ACPIDMAP_VID3RD_S_s
{
    uint32_t              :  4;  /* *UNDEFINED* */
    const uint32_t  user  :  5;  /* ARUSER value to SCU (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  page  :  2;  /* ARADDR 1GB Page Decoder (Status) */
    uint32_t              :  2;  /* *UNDEFINED* */
    const uint32_t  mid   : 12;  /* Remap Master ID (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  force :  1;  /* Force Mapping (Status) */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID3RD_S. */
typedef volatile struct ALT_ACPIDMAP_VID3RD_S_s  ALT_ACPIDMAP_VID3RD_S_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID3RD_S register from the beginning of the component. */
#define ALT_ACPIDMAP_VID3RD_S_OFST        0x38

/*
 * Register : Write AXI Master Mapping Status Register for Fixed Virtual ID 3 - vid3wr_s
 * 
 * The Write AXI Master Mapping Status Register contains the configured USER, ADDR
 * page, and ID signals mapping values for particular transaction with 12-bit ID
 * which locks the fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                     
 * :--------|:-------|:--------|:---------------------------------
 *  [3:0]   | ???    | 0x0     | *UNDEFINED*                     
 *  [8:4]   | R      | Unknown | AWUSER value to SCU (Status)    
 *  [11:9]  | ???    | 0x0     | *UNDEFINED*                     
 *  [13:12] | R      | Unknown | AWADDR 1GB Page Decoder (Status)
 *  [15:14] | ???    | 0x0     | *UNDEFINED*                     
 *  [27:16] | R      | Unknown | Remap Master ID (Status)        
 *  [30:28] | ???    | 0x0     | *UNDEFINED*                     
 *  [31]    | R      | Unknown | Force Mapping (Status)          
 * 
 */
/*
 * Field : AWUSER value to SCU (Status) - user
 * 
 * This value is propagated to SCU as AWUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3WR_S_USER register field. */
#define ALT_ACPIDMAP_VID3WR_S_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3WR_S_USER register field. */
#define ALT_ACPIDMAP_VID3WR_S_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID3WR_S_USER register field. */
#define ALT_ACPIDMAP_VID3WR_S_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID3WR_S_USER register field value. */
#define ALT_ACPIDMAP_VID3WR_S_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID3WR_S_USER register field value. */
#define ALT_ACPIDMAP_VID3WR_S_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID3WR_S_USER register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID3WR_S_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3WR_S_USER field value from a register. */
#define ALT_ACPIDMAP_VID3WR_S_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID3WR_S_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3WR_S_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : AWADDR 1GB Page Decoder (Status) - page
 * 
 * AWADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID3WR_S_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID3WR_S_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID3WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID3WR_S_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID3WR_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID3WR_S_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID3WR_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID3WR_S_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID3WR_S_PAGE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID3WR_S_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3WR_S_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID3WR_S_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID3WR_S_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3WR_S_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID (Status) - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3WR_S_MID register field. */
#define ALT_ACPIDMAP_VID3WR_S_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3WR_S_MID register field. */
#define ALT_ACPIDMAP_VID3WR_S_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID3WR_S_MID register field. */
#define ALT_ACPIDMAP_VID3WR_S_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID3WR_S_MID register field value. */
#define ALT_ACPIDMAP_VID3WR_S_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID3WR_S_MID register field value. */
#define ALT_ACPIDMAP_VID3WR_S_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID3WR_S_MID register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID3WR_S_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3WR_S_MID field value from a register. */
#define ALT_ACPIDMAP_VID3WR_S_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID3WR_S_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3WR_S_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping (Status) - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID3WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID3WR_S_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID3WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID3WR_S_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID3WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID3WR_S_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID3WR_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID3WR_S_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID3WR_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID3WR_S_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID3WR_S_FORCE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID3WR_S_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID3WR_S_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID3WR_S_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID3WR_S_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID3WR_S_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID3WR_S.
 */
struct ALT_ACPIDMAP_VID3WR_S_s
{
    uint32_t              :  4;  /* *UNDEFINED* */
    const uint32_t  user  :  5;  /* AWUSER value to SCU (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  page  :  2;  /* AWADDR 1GB Page Decoder (Status) */
    uint32_t              :  2;  /* *UNDEFINED* */
    const uint32_t  mid   : 12;  /* Remap Master ID (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  force :  1;  /* Force Mapping (Status) */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID3WR_S. */
typedef volatile struct ALT_ACPIDMAP_VID3WR_S_s  ALT_ACPIDMAP_VID3WR_S_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID3WR_S register from the beginning of the component. */
#define ALT_ACPIDMAP_VID3WR_S_OFST        0x3c

/*
 * Register : Read AXI Master Mapping Status Register for Fixed Virtual ID 4 - vid4rd_s
 * 
 * The Read AXI Master Mapping Status Register contains the configured USER, ADDR
 * page, and ID signals mapping values for particular transaction with 12-bit ID
 * which locks the fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                     
 * :--------|:-------|:--------|:---------------------------------
 *  [3:0]   | ???    | 0x0     | *UNDEFINED*                     
 *  [8:4]   | R      | Unknown | ARUSER value to SCU (Status)    
 *  [11:9]  | ???    | 0x0     | *UNDEFINED*                     
 *  [13:12] | R      | Unknown | ARADDR 1GB Page Decoder (Status)
 *  [15:14] | ???    | 0x0     | *UNDEFINED*                     
 *  [27:16] | R      | Unknown | Remap Master ID (Status)        
 *  [30:28] | ???    | 0x0     | *UNDEFINED*                     
 *  [31]    | R      | Unknown | Force Mapping (Status)          
 * 
 */
/*
 * Field : ARUSER value to SCU (Status) - user
 * 
 * This value is propagated to SCU as ARUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4RD_S_USER register field. */
#define ALT_ACPIDMAP_VID4RD_S_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4RD_S_USER register field. */
#define ALT_ACPIDMAP_VID4RD_S_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID4RD_S_USER register field. */
#define ALT_ACPIDMAP_VID4RD_S_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID4RD_S_USER register field value. */
#define ALT_ACPIDMAP_VID4RD_S_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID4RD_S_USER register field value. */
#define ALT_ACPIDMAP_VID4RD_S_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID4RD_S_USER register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID4RD_S_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4RD_S_USER field value from a register. */
#define ALT_ACPIDMAP_VID4RD_S_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID4RD_S_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4RD_S_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : ARADDR 1GB Page Decoder (Status) - page
 * 
 * ARADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID4RD_S_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID4RD_S_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID4RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID4RD_S_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID4RD_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID4RD_S_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID4RD_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID4RD_S_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID4RD_S_PAGE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID4RD_S_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4RD_S_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID4RD_S_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID4RD_S_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4RD_S_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID (Status) - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4RD_S_MID register field. */
#define ALT_ACPIDMAP_VID4RD_S_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4RD_S_MID register field. */
#define ALT_ACPIDMAP_VID4RD_S_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID4RD_S_MID register field. */
#define ALT_ACPIDMAP_VID4RD_S_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID4RD_S_MID register field value. */
#define ALT_ACPIDMAP_VID4RD_S_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID4RD_S_MID register field value. */
#define ALT_ACPIDMAP_VID4RD_S_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID4RD_S_MID register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID4RD_S_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4RD_S_MID field value from a register. */
#define ALT_ACPIDMAP_VID4RD_S_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID4RD_S_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4RD_S_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping (Status) - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID4RD_S_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID4RD_S_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID4RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID4RD_S_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID4RD_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID4RD_S_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID4RD_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID4RD_S_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID4RD_S_FORCE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID4RD_S_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4RD_S_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID4RD_S_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID4RD_S_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4RD_S_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID4RD_S.
 */
struct ALT_ACPIDMAP_VID4RD_S_s
{
    uint32_t              :  4;  /* *UNDEFINED* */
    const uint32_t  user  :  5;  /* ARUSER value to SCU (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  page  :  2;  /* ARADDR 1GB Page Decoder (Status) */
    uint32_t              :  2;  /* *UNDEFINED* */
    const uint32_t  mid   : 12;  /* Remap Master ID (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  force :  1;  /* Force Mapping (Status) */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID4RD_S. */
typedef volatile struct ALT_ACPIDMAP_VID4RD_S_s  ALT_ACPIDMAP_VID4RD_S_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID4RD_S register from the beginning of the component. */
#define ALT_ACPIDMAP_VID4RD_S_OFST        0x40

/*
 * Register : Write AXI Master Mapping Status Register for Fixed Virtual ID 4 - vid4wr_s
 * 
 * The Write AXI Master Mapping Status Register contains the configured USER, ADDR
 * page, and ID signals mapping values for particular transaction with 12-bit ID
 * which locks the fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                     
 * :--------|:-------|:--------|:---------------------------------
 *  [3:0]   | ???    | 0x0     | *UNDEFINED*                     
 *  [8:4]   | R      | Unknown | AWUSER value to SCU (Status)    
 *  [11:9]  | ???    | 0x0     | *UNDEFINED*                     
 *  [13:12] | R      | Unknown | AWADDR 1GB Page Decoder (Status)
 *  [15:14] | ???    | 0x0     | *UNDEFINED*                     
 *  [27:16] | R      | Unknown | Remap Master ID (Status)        
 *  [30:28] | ???    | 0x0     | *UNDEFINED*                     
 *  [31]    | R      | Unknown | Force Mapping (Status)          
 * 
 */
/*
 * Field : AWUSER value to SCU (Status) - user
 * 
 * This value is propagated to SCU as AWUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4WR_S_USER register field. */
#define ALT_ACPIDMAP_VID4WR_S_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4WR_S_USER register field. */
#define ALT_ACPIDMAP_VID4WR_S_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID4WR_S_USER register field. */
#define ALT_ACPIDMAP_VID4WR_S_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID4WR_S_USER register field value. */
#define ALT_ACPIDMAP_VID4WR_S_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID4WR_S_USER register field value. */
#define ALT_ACPIDMAP_VID4WR_S_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID4WR_S_USER register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID4WR_S_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4WR_S_USER field value from a register. */
#define ALT_ACPIDMAP_VID4WR_S_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID4WR_S_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4WR_S_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : AWADDR 1GB Page Decoder (Status) - page
 * 
 * AWADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID4WR_S_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID4WR_S_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID4WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID4WR_S_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID4WR_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID4WR_S_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID4WR_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID4WR_S_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID4WR_S_PAGE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID4WR_S_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4WR_S_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID4WR_S_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID4WR_S_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4WR_S_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID (Status) - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4WR_S_MID register field. */
#define ALT_ACPIDMAP_VID4WR_S_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4WR_S_MID register field. */
#define ALT_ACPIDMAP_VID4WR_S_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID4WR_S_MID register field. */
#define ALT_ACPIDMAP_VID4WR_S_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID4WR_S_MID register field value. */
#define ALT_ACPIDMAP_VID4WR_S_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID4WR_S_MID register field value. */
#define ALT_ACPIDMAP_VID4WR_S_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID4WR_S_MID register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID4WR_S_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4WR_S_MID field value from a register. */
#define ALT_ACPIDMAP_VID4WR_S_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID4WR_S_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4WR_S_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping (Status) - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID4WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID4WR_S_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID4WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID4WR_S_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID4WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID4WR_S_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID4WR_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID4WR_S_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID4WR_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID4WR_S_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID4WR_S_FORCE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID4WR_S_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID4WR_S_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID4WR_S_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID4WR_S_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID4WR_S_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID4WR_S.
 */
struct ALT_ACPIDMAP_VID4WR_S_s
{
    uint32_t              :  4;  /* *UNDEFINED* */
    const uint32_t  user  :  5;  /* AWUSER value to SCU (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  page  :  2;  /* AWADDR 1GB Page Decoder (Status) */
    uint32_t              :  2;  /* *UNDEFINED* */
    const uint32_t  mid   : 12;  /* Remap Master ID (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  force :  1;  /* Force Mapping (Status) */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID4WR_S. */
typedef volatile struct ALT_ACPIDMAP_VID4WR_S_s  ALT_ACPIDMAP_VID4WR_S_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID4WR_S register from the beginning of the component. */
#define ALT_ACPIDMAP_VID4WR_S_OFST        0x44

/*
 * Register : Read AXI Master Mapping Status Register for Fixed Virtual ID 5 - vid5rd_s
 * 
 * The Read AXI Master Mapping Status Register contains the configured USER, ADDR
 * page, and ID signals mapping values for particular transaction with 12-bit ID
 * which locks the fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                     
 * :--------|:-------|:--------|:---------------------------------
 *  [3:0]   | ???    | 0x0     | *UNDEFINED*                     
 *  [8:4]   | R      | Unknown | ARUSER value to SCU (Status)    
 *  [11:9]  | ???    | 0x0     | *UNDEFINED*                     
 *  [13:12] | R      | Unknown | ARADDR 1GB Page Decoder (Status)
 *  [15:14] | ???    | 0x0     | *UNDEFINED*                     
 *  [27:16] | R      | Unknown | Remap Master ID (Status)        
 *  [30:28] | ???    | 0x0     | *UNDEFINED*                     
 *  [31]    | R      | Unknown | Force Mapping (Status)          
 * 
 */
/*
 * Field : ARUSER value to SCU (Status) - user
 * 
 * This value is propagated to SCU as ARUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5RD_S_USER register field. */
#define ALT_ACPIDMAP_VID5RD_S_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5RD_S_USER register field. */
#define ALT_ACPIDMAP_VID5RD_S_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID5RD_S_USER register field. */
#define ALT_ACPIDMAP_VID5RD_S_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID5RD_S_USER register field value. */
#define ALT_ACPIDMAP_VID5RD_S_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID5RD_S_USER register field value. */
#define ALT_ACPIDMAP_VID5RD_S_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID5RD_S_USER register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID5RD_S_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5RD_S_USER field value from a register. */
#define ALT_ACPIDMAP_VID5RD_S_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID5RD_S_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5RD_S_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : ARADDR 1GB Page Decoder (Status) - page
 * 
 * ARADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID5RD_S_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID5RD_S_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID5RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID5RD_S_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID5RD_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID5RD_S_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID5RD_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID5RD_S_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID5RD_S_PAGE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID5RD_S_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5RD_S_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID5RD_S_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID5RD_S_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5RD_S_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID (Status) - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5RD_S_MID register field. */
#define ALT_ACPIDMAP_VID5RD_S_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5RD_S_MID register field. */
#define ALT_ACPIDMAP_VID5RD_S_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID5RD_S_MID register field. */
#define ALT_ACPIDMAP_VID5RD_S_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID5RD_S_MID register field value. */
#define ALT_ACPIDMAP_VID5RD_S_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID5RD_S_MID register field value. */
#define ALT_ACPIDMAP_VID5RD_S_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID5RD_S_MID register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID5RD_S_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5RD_S_MID field value from a register. */
#define ALT_ACPIDMAP_VID5RD_S_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID5RD_S_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5RD_S_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping (Status) - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID5RD_S_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID5RD_S_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID5RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID5RD_S_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID5RD_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID5RD_S_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID5RD_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID5RD_S_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID5RD_S_FORCE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID5RD_S_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5RD_S_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID5RD_S_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID5RD_S_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5RD_S_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID5RD_S.
 */
struct ALT_ACPIDMAP_VID5RD_S_s
{
    uint32_t              :  4;  /* *UNDEFINED* */
    const uint32_t  user  :  5;  /* ARUSER value to SCU (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  page  :  2;  /* ARADDR 1GB Page Decoder (Status) */
    uint32_t              :  2;  /* *UNDEFINED* */
    const uint32_t  mid   : 12;  /* Remap Master ID (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  force :  1;  /* Force Mapping (Status) */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID5RD_S. */
typedef volatile struct ALT_ACPIDMAP_VID5RD_S_s  ALT_ACPIDMAP_VID5RD_S_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID5RD_S register from the beginning of the component. */
#define ALT_ACPIDMAP_VID5RD_S_OFST        0x48

/*
 * Register : Write AXI Master Mapping Status Register for Fixed Virtual ID 5 - vid5wr_s
 * 
 * The Write AXI Master Mapping Status Register contains the configured USER, ADDR
 * page, and ID signals mapping values for particular transaction with 12-bit ID
 * which locks the fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                     
 * :--------|:-------|:--------|:---------------------------------
 *  [3:0]   | ???    | 0x0     | *UNDEFINED*                     
 *  [8:4]   | R      | Unknown | AWUSER value to SCU (Status)    
 *  [11:9]  | ???    | 0x0     | *UNDEFINED*                     
 *  [13:12] | R      | Unknown | AWADDR 1GB Page Decoder (Status)
 *  [15:14] | ???    | 0x0     | *UNDEFINED*                     
 *  [27:16] | R      | Unknown | Remap Master ID (Status)        
 *  [30:28] | ???    | 0x0     | *UNDEFINED*                     
 *  [31]    | R      | Unknown | Force Mapping (Status)          
 * 
 */
/*
 * Field : AWUSER value to SCU (Status) - user
 * 
 * This value is propagated to SCU as AWUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5WR_S_USER register field. */
#define ALT_ACPIDMAP_VID5WR_S_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5WR_S_USER register field. */
#define ALT_ACPIDMAP_VID5WR_S_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID5WR_S_USER register field. */
#define ALT_ACPIDMAP_VID5WR_S_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID5WR_S_USER register field value. */
#define ALT_ACPIDMAP_VID5WR_S_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID5WR_S_USER register field value. */
#define ALT_ACPIDMAP_VID5WR_S_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID5WR_S_USER register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID5WR_S_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5WR_S_USER field value from a register. */
#define ALT_ACPIDMAP_VID5WR_S_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID5WR_S_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5WR_S_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : AWADDR 1GB Page Decoder (Status) - page
 * 
 * AWADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID5WR_S_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID5WR_S_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID5WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID5WR_S_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID5WR_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID5WR_S_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID5WR_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID5WR_S_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID5WR_S_PAGE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID5WR_S_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5WR_S_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID5WR_S_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID5WR_S_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5WR_S_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID (Status) - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5WR_S_MID register field. */
#define ALT_ACPIDMAP_VID5WR_S_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5WR_S_MID register field. */
#define ALT_ACPIDMAP_VID5WR_S_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID5WR_S_MID register field. */
#define ALT_ACPIDMAP_VID5WR_S_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID5WR_S_MID register field value. */
#define ALT_ACPIDMAP_VID5WR_S_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID5WR_S_MID register field value. */
#define ALT_ACPIDMAP_VID5WR_S_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID5WR_S_MID register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID5WR_S_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5WR_S_MID field value from a register. */
#define ALT_ACPIDMAP_VID5WR_S_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID5WR_S_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5WR_S_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping (Status) - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID5WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID5WR_S_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID5WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID5WR_S_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID5WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID5WR_S_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID5WR_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID5WR_S_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID5WR_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID5WR_S_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID5WR_S_FORCE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID5WR_S_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID5WR_S_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID5WR_S_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID5WR_S_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID5WR_S_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID5WR_S.
 */
struct ALT_ACPIDMAP_VID5WR_S_s
{
    uint32_t              :  4;  /* *UNDEFINED* */
    const uint32_t  user  :  5;  /* AWUSER value to SCU (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  page  :  2;  /* AWADDR 1GB Page Decoder (Status) */
    uint32_t              :  2;  /* *UNDEFINED* */
    const uint32_t  mid   : 12;  /* Remap Master ID (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  force :  1;  /* Force Mapping (Status) */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID5WR_S. */
typedef volatile struct ALT_ACPIDMAP_VID5WR_S_s  ALT_ACPIDMAP_VID5WR_S_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID5WR_S register from the beginning of the component. */
#define ALT_ACPIDMAP_VID5WR_S_OFST        0x4c

/*
 * Register : Read AXI Master Mapping Status Register for Fixed Virtual ID 6 - vid6rd_s
 * 
 * The Read AXI Master Mapping Status Register contains the configured USER, ADDR
 * page, and ID signals mapping values for particular transaction with 12-bit ID
 * which locks the fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                     
 * :--------|:-------|:--------|:---------------------------------
 *  [3:0]   | ???    | 0x0     | *UNDEFINED*                     
 *  [8:4]   | R      | Unknown | ARUSER value to SCU (Status)    
 *  [11:9]  | ???    | 0x0     | *UNDEFINED*                     
 *  [13:12] | R      | Unknown | ARADDR 1GB Page Decoder (Status)
 *  [15:14] | ???    | 0x0     | *UNDEFINED*                     
 *  [27:16] | R      | Unknown | Remap Master ID (Status)        
 *  [30:28] | ???    | 0x0     | *UNDEFINED*                     
 *  [31]    | R      | Unknown | Force Mapping (Status)          
 * 
 */
/*
 * Field : ARUSER value to SCU (Status) - user
 * 
 * This value is propagated to SCU as ARUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6RD_S_USER register field. */
#define ALT_ACPIDMAP_VID6RD_S_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6RD_S_USER register field. */
#define ALT_ACPIDMAP_VID6RD_S_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID6RD_S_USER register field. */
#define ALT_ACPIDMAP_VID6RD_S_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID6RD_S_USER register field value. */
#define ALT_ACPIDMAP_VID6RD_S_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID6RD_S_USER register field value. */
#define ALT_ACPIDMAP_VID6RD_S_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID6RD_S_USER register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID6RD_S_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6RD_S_USER field value from a register. */
#define ALT_ACPIDMAP_VID6RD_S_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID6RD_S_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6RD_S_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : ARADDR 1GB Page Decoder (Status) - page
 * 
 * ARADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID6RD_S_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID6RD_S_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID6RD_S_PAGE register field. */
#define ALT_ACPIDMAP_VID6RD_S_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID6RD_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID6RD_S_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID6RD_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID6RD_S_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID6RD_S_PAGE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID6RD_S_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6RD_S_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID6RD_S_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID6RD_S_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6RD_S_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID (Status) - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6RD_S_MID register field. */
#define ALT_ACPIDMAP_VID6RD_S_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6RD_S_MID register field. */
#define ALT_ACPIDMAP_VID6RD_S_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID6RD_S_MID register field. */
#define ALT_ACPIDMAP_VID6RD_S_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID6RD_S_MID register field value. */
#define ALT_ACPIDMAP_VID6RD_S_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID6RD_S_MID register field value. */
#define ALT_ACPIDMAP_VID6RD_S_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID6RD_S_MID register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID6RD_S_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6RD_S_MID field value from a register. */
#define ALT_ACPIDMAP_VID6RD_S_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID6RD_S_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6RD_S_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping (Status) - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID6RD_S_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID6RD_S_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID6RD_S_FORCE register field. */
#define ALT_ACPIDMAP_VID6RD_S_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID6RD_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID6RD_S_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID6RD_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID6RD_S_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID6RD_S_FORCE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID6RD_S_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6RD_S_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID6RD_S_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID6RD_S_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6RD_S_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID6RD_S.
 */
struct ALT_ACPIDMAP_VID6RD_S_s
{
    uint32_t              :  4;  /* *UNDEFINED* */
    const uint32_t  user  :  5;  /* ARUSER value to SCU (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  page  :  2;  /* ARADDR 1GB Page Decoder (Status) */
    uint32_t              :  2;  /* *UNDEFINED* */
    const uint32_t  mid   : 12;  /* Remap Master ID (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  force :  1;  /* Force Mapping (Status) */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID6RD_S. */
typedef volatile struct ALT_ACPIDMAP_VID6RD_S_s  ALT_ACPIDMAP_VID6RD_S_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID6RD_S register from the beginning of the component. */
#define ALT_ACPIDMAP_VID6RD_S_OFST        0x50

/*
 * Register : Write AXI Master Mapping Status Register for Fixed Virtual ID 6 - vid6wr_s
 * 
 * The Write AXI Master Mapping Status Register contains the configured USER, ADDR
 * page, and ID signals mapping values for particular transaction with 12-bit ID
 * which locks the fixed 3-bit virtual ID.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                     
 * :--------|:-------|:--------|:---------------------------------
 *  [3:0]   | ???    | 0x0     | *UNDEFINED*                     
 *  [8:4]   | R      | Unknown | AWUSER value to SCU (Status)    
 *  [11:9]  | ???    | 0x0     | *UNDEFINED*                     
 *  [13:12] | R      | Unknown | AWADDR 1GB Page Decoder (Status)
 *  [15:14] | ???    | 0x0     | *UNDEFINED*                     
 *  [27:16] | R      | Unknown | Remap Master ID (Status)        
 *  [30:28] | ???    | 0x0     | *UNDEFINED*                     
 *  [31]    | R      | Unknown | Force Mapping (Status)          
 * 
 */
/*
 * Field : AWUSER value to SCU (Status) - user
 * 
 * This value is propagated to SCU as AWUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6WR_S_USER register field. */
#define ALT_ACPIDMAP_VID6WR_S_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6WR_S_USER register field. */
#define ALT_ACPIDMAP_VID6WR_S_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_VID6WR_S_USER register field. */
#define ALT_ACPIDMAP_VID6WR_S_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_VID6WR_S_USER register field value. */
#define ALT_ACPIDMAP_VID6WR_S_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_VID6WR_S_USER register field value. */
#define ALT_ACPIDMAP_VID6WR_S_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_VID6WR_S_USER register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID6WR_S_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6WR_S_USER field value from a register. */
#define ALT_ACPIDMAP_VID6WR_S_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_VID6WR_S_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6WR_S_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : AWADDR 1GB Page Decoder (Status) - page
 * 
 * AWADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID6WR_S_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID6WR_S_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_VID6WR_S_PAGE register field. */
#define ALT_ACPIDMAP_VID6WR_S_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_VID6WR_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID6WR_S_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_VID6WR_S_PAGE register field value. */
#define ALT_ACPIDMAP_VID6WR_S_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_VID6WR_S_PAGE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID6WR_S_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6WR_S_PAGE field value from a register. */
#define ALT_ACPIDMAP_VID6WR_S_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_VID6WR_S_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6WR_S_PAGE_SET(value) (((value) << 12) & 0x00003000)

/*
 * Field : Remap Master ID (Status) - mid
 * 
 * The 12-bit ID of the master to remap to 3-bit virtual ID N, where N is the 3-bit
 * ID to use.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6WR_S_MID register field. */
#define ALT_ACPIDMAP_VID6WR_S_MID_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6WR_S_MID register field. */
#define ALT_ACPIDMAP_VID6WR_S_MID_MSB        27
/* The width in bits of the ALT_ACPIDMAP_VID6WR_S_MID register field. */
#define ALT_ACPIDMAP_VID6WR_S_MID_WIDTH      12
/* The mask used to set the ALT_ACPIDMAP_VID6WR_S_MID register field value. */
#define ALT_ACPIDMAP_VID6WR_S_MID_SET_MSK    0x0fff0000
/* The mask used to clear the ALT_ACPIDMAP_VID6WR_S_MID register field value. */
#define ALT_ACPIDMAP_VID6WR_S_MID_CLR_MSK    0xf000ffff
/* The reset value of the ALT_ACPIDMAP_VID6WR_S_MID register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID6WR_S_MID_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6WR_S_MID field value from a register. */
#define ALT_ACPIDMAP_VID6WR_S_MID_GET(value) (((value) & 0x0fff0000) >> 16)
/* Produces a ALT_ACPIDMAP_VID6WR_S_MID register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6WR_S_MID_SET(value) (((value) << 16) & 0x0fff0000)

/*
 * Field : Force Mapping (Status) - force
 * 
 * Set to 1 to force the mapping between the 12-bit ID and 3-bit virtual ID N. Set
 * to 0 to allow the 3-bit ID N to be dynamically allocated.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_VID6WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID6WR_S_FORCE_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_VID6WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID6WR_S_FORCE_MSB        31
/* The width in bits of the ALT_ACPIDMAP_VID6WR_S_FORCE register field. */
#define ALT_ACPIDMAP_VID6WR_S_FORCE_WIDTH      1
/* The mask used to set the ALT_ACPIDMAP_VID6WR_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID6WR_S_FORCE_SET_MSK    0x80000000
/* The mask used to clear the ALT_ACPIDMAP_VID6WR_S_FORCE register field value. */
#define ALT_ACPIDMAP_VID6WR_S_FORCE_CLR_MSK    0x7fffffff
/* The reset value of the ALT_ACPIDMAP_VID6WR_S_FORCE register field is UNKNOWN. */
#define ALT_ACPIDMAP_VID6WR_S_FORCE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_VID6WR_S_FORCE field value from a register. */
#define ALT_ACPIDMAP_VID6WR_S_FORCE_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_ACPIDMAP_VID6WR_S_FORCE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_VID6WR_S_FORCE_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_VID6WR_S.
 */
struct ALT_ACPIDMAP_VID6WR_S_s
{
    uint32_t              :  4;  /* *UNDEFINED* */
    const uint32_t  user  :  5;  /* AWUSER value to SCU (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  page  :  2;  /* AWADDR 1GB Page Decoder (Status) */
    uint32_t              :  2;  /* *UNDEFINED* */
    const uint32_t  mid   : 12;  /* Remap Master ID (Status) */
    uint32_t              :  3;  /* *UNDEFINED* */
    const uint32_t  force :  1;  /* Force Mapping (Status) */
};

/* The typedef declaration for register ALT_ACPIDMAP_VID6WR_S. */
typedef volatile struct ALT_ACPIDMAP_VID6WR_S_s  ALT_ACPIDMAP_VID6WR_S_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_VID6WR_S register from the beginning of the component. */
#define ALT_ACPIDMAP_VID6WR_S_OFST        0x54

/*
 * Register : Read AXI Master Mapping Status Register for Dynamic Virtual ID Remap - dynrd_s
 * 
 * The Read AXI Master Mapping Status Register contains the configured USER, and
 * ADDR page signals mapping values for transaction that dynamically remapped to
 * one of the available 3-bit virtual IDs.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                     
 * :--------|:-------|:--------|:---------------------------------
 *  [3:0]   | ???    | 0x0     | *UNDEFINED*                     
 *  [8:4]   | R      | Unknown | ARUSER value to SCU (Status)    
 *  [11:9]  | ???    | 0x0     | *UNDEFINED*                     
 *  [13:12] | R      | Unknown | ARADDR 1GB Page Decoder (Status)
 *  [31:14] | ???    | 0x0     | *UNDEFINED*                     
 * 
 */
/*
 * Field : ARUSER value to SCU (Status) - user
 * 
 * This value is propagated to SCU as ARUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_DYNRD_S_USER register field. */
#define ALT_ACPIDMAP_DYNRD_S_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_DYNRD_S_USER register field. */
#define ALT_ACPIDMAP_DYNRD_S_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_DYNRD_S_USER register field. */
#define ALT_ACPIDMAP_DYNRD_S_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_DYNRD_S_USER register field value. */
#define ALT_ACPIDMAP_DYNRD_S_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_DYNRD_S_USER register field value. */
#define ALT_ACPIDMAP_DYNRD_S_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_DYNRD_S_USER register field is UNKNOWN. */
#define ALT_ACPIDMAP_DYNRD_S_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_DYNRD_S_USER field value from a register. */
#define ALT_ACPIDMAP_DYNRD_S_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_DYNRD_S_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_DYNRD_S_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : ARADDR 1GB Page Decoder (Status) - page
 * 
 * ARADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_DYNRD_S_PAGE register field. */
#define ALT_ACPIDMAP_DYNRD_S_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_DYNRD_S_PAGE register field. */
#define ALT_ACPIDMAP_DYNRD_S_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_DYNRD_S_PAGE register field. */
#define ALT_ACPIDMAP_DYNRD_S_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_DYNRD_S_PAGE register field value. */
#define ALT_ACPIDMAP_DYNRD_S_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_DYNRD_S_PAGE register field value. */
#define ALT_ACPIDMAP_DYNRD_S_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_DYNRD_S_PAGE register field is UNKNOWN. */
#define ALT_ACPIDMAP_DYNRD_S_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_DYNRD_S_PAGE field value from a register. */
#define ALT_ACPIDMAP_DYNRD_S_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_DYNRD_S_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_DYNRD_S_PAGE_SET(value) (((value) << 12) & 0x00003000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_DYNRD_S.
 */
struct ALT_ACPIDMAP_DYNRD_S_s
{
    uint32_t             :  4;  /* *UNDEFINED* */
    const uint32_t  user :  5;  /* ARUSER value to SCU (Status) */
    uint32_t             :  3;  /* *UNDEFINED* */
    const uint32_t  page :  2;  /* ARADDR 1GB Page Decoder (Status) */
    uint32_t             : 18;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_ACPIDMAP_DYNRD_S. */
typedef volatile struct ALT_ACPIDMAP_DYNRD_S_s  ALT_ACPIDMAP_DYNRD_S_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_DYNRD_S register from the beginning of the component. */
#define ALT_ACPIDMAP_DYNRD_S_OFST        0x58

/*
 * Register : Write AXI Master Mapping Status Register for Dynamic Virtual ID Remap - dynwr_s
 * 
 * The Write AXI Master Mapping Status Register contains the configured USER, and
 * ADDR page signals mapping values for transaction that dynamically remapped to
 * one of the available 3-bit virtual IDs.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                     
 * :--------|:-------|:--------|:---------------------------------
 *  [3:0]   | ???    | 0x0     | *UNDEFINED*                     
 *  [8:4]   | R      | Unknown | AWUSER value to SCU (Status)    
 *  [11:9]  | ???    | 0x0     | *UNDEFINED*                     
 *  [13:12] | R      | Unknown | AWADDR 1GB Page Decoder (Status)
 *  [31:14] | ???    | 0x0     | *UNDEFINED*                     
 * 
 */
/*
 * Field : AWUSER value to SCU (Status) - user
 * 
 * This value is propagated to SCU as AWUSERS.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_DYNWR_S_USER register field. */
#define ALT_ACPIDMAP_DYNWR_S_USER_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_DYNWR_S_USER register field. */
#define ALT_ACPIDMAP_DYNWR_S_USER_MSB        8
/* The width in bits of the ALT_ACPIDMAP_DYNWR_S_USER register field. */
#define ALT_ACPIDMAP_DYNWR_S_USER_WIDTH      5
/* The mask used to set the ALT_ACPIDMAP_DYNWR_S_USER register field value. */
#define ALT_ACPIDMAP_DYNWR_S_USER_SET_MSK    0x000001f0
/* The mask used to clear the ALT_ACPIDMAP_DYNWR_S_USER register field value. */
#define ALT_ACPIDMAP_DYNWR_S_USER_CLR_MSK    0xfffffe0f
/* The reset value of the ALT_ACPIDMAP_DYNWR_S_USER register field is UNKNOWN. */
#define ALT_ACPIDMAP_DYNWR_S_USER_RESET      0x0
/* Extracts the ALT_ACPIDMAP_DYNWR_S_USER field value from a register. */
#define ALT_ACPIDMAP_DYNWR_S_USER_GET(value) (((value) & 0x000001f0) >> 4)
/* Produces a ALT_ACPIDMAP_DYNWR_S_USER register field value suitable for setting the register. */
#define ALT_ACPIDMAP_DYNWR_S_USER_SET(value) (((value) << 4) & 0x000001f0)

/*
 * Field : AWADDR 1GB Page Decoder (Status) - page
 * 
 * AWADDR remap to 1st, 2nd, 3rd, or 4th 1GB memory region.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_ACPIDMAP_DYNWR_S_PAGE register field. */
#define ALT_ACPIDMAP_DYNWR_S_PAGE_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_ACPIDMAP_DYNWR_S_PAGE register field. */
#define ALT_ACPIDMAP_DYNWR_S_PAGE_MSB        13
/* The width in bits of the ALT_ACPIDMAP_DYNWR_S_PAGE register field. */
#define ALT_ACPIDMAP_DYNWR_S_PAGE_WIDTH      2
/* The mask used to set the ALT_ACPIDMAP_DYNWR_S_PAGE register field value. */
#define ALT_ACPIDMAP_DYNWR_S_PAGE_SET_MSK    0x00003000
/* The mask used to clear the ALT_ACPIDMAP_DYNWR_S_PAGE register field value. */
#define ALT_ACPIDMAP_DYNWR_S_PAGE_CLR_MSK    0xffffcfff
/* The reset value of the ALT_ACPIDMAP_DYNWR_S_PAGE register field is UNKNOWN. */
#define ALT_ACPIDMAP_DYNWR_S_PAGE_RESET      0x0
/* Extracts the ALT_ACPIDMAP_DYNWR_S_PAGE field value from a register. */
#define ALT_ACPIDMAP_DYNWR_S_PAGE_GET(value) (((value) & 0x00003000) >> 12)
/* Produces a ALT_ACPIDMAP_DYNWR_S_PAGE register field value suitable for setting the register. */
#define ALT_ACPIDMAP_DYNWR_S_PAGE_SET(value) (((value) << 12) & 0x00003000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_ACPIDMAP_DYNWR_S.
 */
struct ALT_ACPIDMAP_DYNWR_S_s
{
    uint32_t             :  4;  /* *UNDEFINED* */
    const uint32_t  user :  5;  /* AWUSER value to SCU (Status) */
    uint32_t             :  3;  /* *UNDEFINED* */
    const uint32_t  page :  2;  /* AWADDR 1GB Page Decoder (Status) */
    uint32_t             : 18;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_ACPIDMAP_DYNWR_S. */
typedef volatile struct ALT_ACPIDMAP_DYNWR_S_s  ALT_ACPIDMAP_DYNWR_S_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_ACPIDMAP_DYNWR_S register from the beginning of the component. */
#define ALT_ACPIDMAP_DYNWR_S_OFST        0x5c

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_ACPIDMAP.
 */
struct ALT_ACPIDMAP_s
{
    volatile ALT_ACPIDMAP_VID2RD_t    vid2rd;                  /* ALT_ACPIDMAP_VID2RD */
    volatile ALT_ACPIDMAP_VID2WR_t    vid2wr;                  /* ALT_ACPIDMAP_VID2WR */
    volatile ALT_ACPIDMAP_VID3RD_t    vid3rd;                  /* ALT_ACPIDMAP_VID3RD */
    volatile ALT_ACPIDMAP_VID3WR_t    vid3wr;                  /* ALT_ACPIDMAP_VID3WR */
    volatile ALT_ACPIDMAP_VID4RD_t    vid4rd;                  /* ALT_ACPIDMAP_VID4RD */
    volatile ALT_ACPIDMAP_VID4WR_t    vid4wr;                  /* ALT_ACPIDMAP_VID4WR */
    volatile ALT_ACPIDMAP_VID5RD_t    vid5rd;                  /* ALT_ACPIDMAP_VID5RD */
    volatile ALT_ACPIDMAP_VID5WR_t    vid5wr;                  /* ALT_ACPIDMAP_VID5WR */
    volatile ALT_ACPIDMAP_VID6RD_t    vid6rd;                  /* ALT_ACPIDMAP_VID6RD */
    volatile ALT_ACPIDMAP_VID6WR_t    vid6wr;                  /* ALT_ACPIDMAP_VID6WR */
    volatile ALT_ACPIDMAP_DYNRD_t     dynrd;                   /* ALT_ACPIDMAP_DYNRD */
    volatile ALT_ACPIDMAP_DYNWR_t     dynwr;                   /* ALT_ACPIDMAP_DYNWR */
    volatile ALT_ACPIDMAP_VID2RD_S_t  vid2rd_s;                /* ALT_ACPIDMAP_VID2RD_S */
    volatile ALT_ACPIDMAP_VID2WR_S_t  vid2wr_s;                /* ALT_ACPIDMAP_VID2WR_S */
    volatile ALT_ACPIDMAP_VID3RD_S_t  vid3rd_s;                /* ALT_ACPIDMAP_VID3RD_S */
    volatile ALT_ACPIDMAP_VID3WR_S_t  vid3wr_s;                /* ALT_ACPIDMAP_VID3WR_S */
    volatile ALT_ACPIDMAP_VID4RD_S_t  vid4rd_s;                /* ALT_ACPIDMAP_VID4RD_S */
    volatile ALT_ACPIDMAP_VID4WR_S_t  vid4wr_s;                /* ALT_ACPIDMAP_VID4WR_S */
    volatile ALT_ACPIDMAP_VID5RD_S_t  vid5rd_s;                /* ALT_ACPIDMAP_VID5RD_S */
    volatile ALT_ACPIDMAP_VID5WR_S_t  vid5wr_s;                /* ALT_ACPIDMAP_VID5WR_S */
    volatile ALT_ACPIDMAP_VID6RD_S_t  vid6rd_s;                /* ALT_ACPIDMAP_VID6RD_S */
    volatile ALT_ACPIDMAP_VID6WR_S_t  vid6wr_s;                /* ALT_ACPIDMAP_VID6WR_S */
    volatile ALT_ACPIDMAP_DYNRD_S_t   dynrd_s;                 /* ALT_ACPIDMAP_DYNRD_S */
    volatile ALT_ACPIDMAP_DYNWR_S_t   dynwr_s;                 /* ALT_ACPIDMAP_DYNWR_S */
    volatile uint32_t                 _pad_0x60_0x1000[1000];  /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_ACPIDMAP. */
typedef volatile struct ALT_ACPIDMAP_s  ALT_ACPIDMAP_t;
/* The struct declaration for the raw register contents of register group ALT_ACPIDMAP. */
struct ALT_ACPIDMAP_raw_s
{
    volatile uint32_t  vid2rd;                  /* ALT_ACPIDMAP_VID2RD */
    volatile uint32_t  vid2wr;                  /* ALT_ACPIDMAP_VID2WR */
    volatile uint32_t  vid3rd;                  /* ALT_ACPIDMAP_VID3RD */
    volatile uint32_t  vid3wr;                  /* ALT_ACPIDMAP_VID3WR */
    volatile uint32_t  vid4rd;                  /* ALT_ACPIDMAP_VID4RD */
    volatile uint32_t  vid4wr;                  /* ALT_ACPIDMAP_VID4WR */
    volatile uint32_t  vid5rd;                  /* ALT_ACPIDMAP_VID5RD */
    volatile uint32_t  vid5wr;                  /* ALT_ACPIDMAP_VID5WR */
    volatile uint32_t  vid6rd;                  /* ALT_ACPIDMAP_VID6RD */
    volatile uint32_t  vid6wr;                  /* ALT_ACPIDMAP_VID6WR */
    volatile uint32_t  dynrd;                   /* ALT_ACPIDMAP_DYNRD */
    volatile uint32_t  dynwr;                   /* ALT_ACPIDMAP_DYNWR */
    volatile uint32_t  vid2rd_s;                /* ALT_ACPIDMAP_VID2RD_S */
    volatile uint32_t  vid2wr_s;                /* ALT_ACPIDMAP_VID2WR_S */
    volatile uint32_t  vid3rd_s;                /* ALT_ACPIDMAP_VID3RD_S */
    volatile uint32_t  vid3wr_s;                /* ALT_ACPIDMAP_VID3WR_S */
    volatile uint32_t  vid4rd_s;                /* ALT_ACPIDMAP_VID4RD_S */
    volatile uint32_t  vid4wr_s;                /* ALT_ACPIDMAP_VID4WR_S */
    volatile uint32_t  vid5rd_s;                /* ALT_ACPIDMAP_VID5RD_S */
    volatile uint32_t  vid5wr_s;                /* ALT_ACPIDMAP_VID5WR_S */
    volatile uint32_t  vid6rd_s;                /* ALT_ACPIDMAP_VID6RD_S */
    volatile uint32_t  vid6wr_s;                /* ALT_ACPIDMAP_VID6WR_S */
    volatile uint32_t  dynrd_s;                 /* ALT_ACPIDMAP_DYNRD_S */
    volatile uint32_t  dynwr_s;                 /* ALT_ACPIDMAP_DYNWR_S */
    volatile uint32_t  _pad_0x60_0x1000[1000];  /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_ACPIDMAP. */
typedef volatile struct ALT_ACPIDMAP_raw_s  ALT_ACPIDMAP_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_ACPIDMAP_H__ */

