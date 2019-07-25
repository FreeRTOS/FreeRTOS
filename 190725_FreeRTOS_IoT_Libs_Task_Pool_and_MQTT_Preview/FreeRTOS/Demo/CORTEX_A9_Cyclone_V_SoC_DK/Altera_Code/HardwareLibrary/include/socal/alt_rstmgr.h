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

/* Altera - ALT_RSTMGR */

#ifndef __ALTERA_ALT_RSTMGR_H__
#define __ALTERA_ALT_RSTMGR_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : Reset Manager Module - ALT_RSTMGR
 * Reset Manager Module
 * 
 * Registers in the Reset Manager module
 * 
 */
/*
 * Register : Status Register - stat
 * 
 * The STAT register contains bits that indicate the reset source or a timeout
 * event. For reset sources, a field is 1 if its associated reset requester caused
 * the reset. For timeout events, a field is 1 if its associated timeout occured as
 * part of a hardware sequenced warm/debug reset.
 * 
 * Software clears bits by writing them with a value of 1. Writes to bits with a
 * value of 0 are ignored.
 * 
 * After a cold reset is complete, all bits are reset to their reset value except
 * for the bit(s) that indicate the source of the cold reset. If multiple cold
 * reset requests overlap with each other, the source de-asserts the request last
 * will be logged. The other reset request source(s)  de-assert the request in the
 * same cycle will also be logged, the rest of the fields are reset to default
 * value of 0.
 * 
 * After a warm reset is complete, the bit(s) that indicate the source of  the warm
 * reset are set to 1. A warm reset doesn't clear any of the bits  in the STAT
 * register; these bits must be cleared by software writing  the STAT register.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                         
 * :--------|:-------|:------|:-------------------------------------
 *  [0]     | RW     | 0x0   | Power-On Voltage Detector Cold Reset
 *  [1]     | RW     | 0x0   | nPOR Pin Cold Reset                 
 *  [2]     | RW     | 0x0   | FPGA Core Cold Reset                
 *  [3]     | RW     | 0x0   | CONFIG_IO Cold Reset                
 *  [4]     | RW     | 0x0   | Software Cold Reset                 
 *  [7:5]   | ???    | 0x0   | *UNDEFINED*                         
 *  [8]     | RW     | 0x0   | nRST Pin Warm Reset                 
 *  [9]     | RW     | 0x0   | FPGA Core Warm Reset                
 *  [10]    | RW     | 0x0   | Software Warm Reset                 
 *  [11]    | ???    | 0x0   | *UNDEFINED*                         
 *  [12]    | RW     | 0x0   | MPU Watchdog 0 Warm Reset           
 *  [13]    | RW     | 0x0   | MPU Watchdog 1 Warm Reset           
 *  [14]    | RW     | 0x0   | L4 Watchdog 0 Warm Reset            
 *  [15]    | RW     | 0x0   | L4 Watchdog 1 Warm Reset            
 *  [17:16] | ???    | 0x0   | *UNDEFINED*                         
 *  [18]    | RW     | 0x0   | FPGA Core Debug Reset               
 *  [19]    | RW     | 0x0   | DAP Debug Reset                     
 *  [23:20] | ???    | 0x0   | *UNDEFINED*                         
 *  [24]    | RW     | 0x0   | SDRAM Self-Refresh Timeout          
 *  [25]    | RW     | 0x0   | FPGA manager handshake Timeout      
 *  [26]    | RW     | 0x0   | SCAN manager handshake Timeout      
 *  [27]    | RW     | 0x0   | FPGA handshake Timeout              
 *  [28]    | RW     | 0x0   | ETR Stall Timeout                   
 *  [31:29] | ???    | 0x0   | *UNDEFINED*                         
 * 
 */
/*
 * Field : Power-On Voltage Detector Cold Reset - porvoltrst
 * 
 * Built-in POR voltage detector triggered a cold reset (por_voltage_req = 1)
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_PORVOLTRST register field. */
#define ALT_RSTMGR_STAT_PORVOLTRST_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_PORVOLTRST register field. */
#define ALT_RSTMGR_STAT_PORVOLTRST_MSB        0
/* The width in bits of the ALT_RSTMGR_STAT_PORVOLTRST register field. */
#define ALT_RSTMGR_STAT_PORVOLTRST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_PORVOLTRST register field value. */
#define ALT_RSTMGR_STAT_PORVOLTRST_SET_MSK    0x00000001
/* The mask used to clear the ALT_RSTMGR_STAT_PORVOLTRST register field value. */
#define ALT_RSTMGR_STAT_PORVOLTRST_CLR_MSK    0xfffffffe
/* The reset value of the ALT_RSTMGR_STAT_PORVOLTRST register field. */
#define ALT_RSTMGR_STAT_PORVOLTRST_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_PORVOLTRST field value from a register. */
#define ALT_RSTMGR_STAT_PORVOLTRST_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_RSTMGR_STAT_PORVOLTRST register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_PORVOLTRST_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : nPOR Pin Cold Reset - nporpinrst
 * 
 * nPOR pin triggered a cold reset (por_pin_req = 1)
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_NPORPINRST register field. */
#define ALT_RSTMGR_STAT_NPORPINRST_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_NPORPINRST register field. */
#define ALT_RSTMGR_STAT_NPORPINRST_MSB        1
/* The width in bits of the ALT_RSTMGR_STAT_NPORPINRST register field. */
#define ALT_RSTMGR_STAT_NPORPINRST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_NPORPINRST register field value. */
#define ALT_RSTMGR_STAT_NPORPINRST_SET_MSK    0x00000002
/* The mask used to clear the ALT_RSTMGR_STAT_NPORPINRST register field value. */
#define ALT_RSTMGR_STAT_NPORPINRST_CLR_MSK    0xfffffffd
/* The reset value of the ALT_RSTMGR_STAT_NPORPINRST register field. */
#define ALT_RSTMGR_STAT_NPORPINRST_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_NPORPINRST field value from a register. */
#define ALT_RSTMGR_STAT_NPORPINRST_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_RSTMGR_STAT_NPORPINRST register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_NPORPINRST_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : FPGA Core Cold Reset - fpgacoldrst
 * 
 * FPGA core triggered a cold reset (f2h_cold_rst_req_n = 1)
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_FPGACOLDRST register field. */
#define ALT_RSTMGR_STAT_FPGACOLDRST_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_FPGACOLDRST register field. */
#define ALT_RSTMGR_STAT_FPGACOLDRST_MSB        2
/* The width in bits of the ALT_RSTMGR_STAT_FPGACOLDRST register field. */
#define ALT_RSTMGR_STAT_FPGACOLDRST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_FPGACOLDRST register field value. */
#define ALT_RSTMGR_STAT_FPGACOLDRST_SET_MSK    0x00000004
/* The mask used to clear the ALT_RSTMGR_STAT_FPGACOLDRST register field value. */
#define ALT_RSTMGR_STAT_FPGACOLDRST_CLR_MSK    0xfffffffb
/* The reset value of the ALT_RSTMGR_STAT_FPGACOLDRST register field. */
#define ALT_RSTMGR_STAT_FPGACOLDRST_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_FPGACOLDRST field value from a register. */
#define ALT_RSTMGR_STAT_FPGACOLDRST_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_RSTMGR_STAT_FPGACOLDRST register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_FPGACOLDRST_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : CONFIG_IO Cold Reset - configiocoldrst
 * 
 * FPGA entered CONFIG_IO mode and a triggered a cold reset
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_CFGIOCOLDRST register field. */
#define ALT_RSTMGR_STAT_CFGIOCOLDRST_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_CFGIOCOLDRST register field. */
#define ALT_RSTMGR_STAT_CFGIOCOLDRST_MSB        3
/* The width in bits of the ALT_RSTMGR_STAT_CFGIOCOLDRST register field. */
#define ALT_RSTMGR_STAT_CFGIOCOLDRST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_CFGIOCOLDRST register field value. */
#define ALT_RSTMGR_STAT_CFGIOCOLDRST_SET_MSK    0x00000008
/* The mask used to clear the ALT_RSTMGR_STAT_CFGIOCOLDRST register field value. */
#define ALT_RSTMGR_STAT_CFGIOCOLDRST_CLR_MSK    0xfffffff7
/* The reset value of the ALT_RSTMGR_STAT_CFGIOCOLDRST register field. */
#define ALT_RSTMGR_STAT_CFGIOCOLDRST_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_CFGIOCOLDRST field value from a register. */
#define ALT_RSTMGR_STAT_CFGIOCOLDRST_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_RSTMGR_STAT_CFGIOCOLDRST register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_CFGIOCOLDRST_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Software Cold Reset - swcoldrst
 * 
 * Software wrote CTRL.SWCOLDRSTREQ to 1 and triggered a cold reset
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_SWCOLDRST register field. */
#define ALT_RSTMGR_STAT_SWCOLDRST_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_SWCOLDRST register field. */
#define ALT_RSTMGR_STAT_SWCOLDRST_MSB        4
/* The width in bits of the ALT_RSTMGR_STAT_SWCOLDRST register field. */
#define ALT_RSTMGR_STAT_SWCOLDRST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_SWCOLDRST register field value. */
#define ALT_RSTMGR_STAT_SWCOLDRST_SET_MSK    0x00000010
/* The mask used to clear the ALT_RSTMGR_STAT_SWCOLDRST register field value. */
#define ALT_RSTMGR_STAT_SWCOLDRST_CLR_MSK    0xffffffef
/* The reset value of the ALT_RSTMGR_STAT_SWCOLDRST register field. */
#define ALT_RSTMGR_STAT_SWCOLDRST_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_SWCOLDRST field value from a register. */
#define ALT_RSTMGR_STAT_SWCOLDRST_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_RSTMGR_STAT_SWCOLDRST register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_SWCOLDRST_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : nRST Pin Warm Reset - nrstpinrst
 * 
 * nRST pin triggered a hardware sequenced warm reset
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_NRSTPINRST register field. */
#define ALT_RSTMGR_STAT_NRSTPINRST_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_NRSTPINRST register field. */
#define ALT_RSTMGR_STAT_NRSTPINRST_MSB        8
/* The width in bits of the ALT_RSTMGR_STAT_NRSTPINRST register field. */
#define ALT_RSTMGR_STAT_NRSTPINRST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_NRSTPINRST register field value. */
#define ALT_RSTMGR_STAT_NRSTPINRST_SET_MSK    0x00000100
/* The mask used to clear the ALT_RSTMGR_STAT_NRSTPINRST register field value. */
#define ALT_RSTMGR_STAT_NRSTPINRST_CLR_MSK    0xfffffeff
/* The reset value of the ALT_RSTMGR_STAT_NRSTPINRST register field. */
#define ALT_RSTMGR_STAT_NRSTPINRST_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_NRSTPINRST field value from a register. */
#define ALT_RSTMGR_STAT_NRSTPINRST_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_RSTMGR_STAT_NRSTPINRST register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_NRSTPINRST_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : FPGA Core Warm Reset - fpgawarmrst
 * 
 * FPGA core triggered a hardware sequenced warm reset (f2h_warm_rst_req_n = 1)
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_FPGAWARMRST register field. */
#define ALT_RSTMGR_STAT_FPGAWARMRST_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_FPGAWARMRST register field. */
#define ALT_RSTMGR_STAT_FPGAWARMRST_MSB        9
/* The width in bits of the ALT_RSTMGR_STAT_FPGAWARMRST register field. */
#define ALT_RSTMGR_STAT_FPGAWARMRST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_FPGAWARMRST register field value. */
#define ALT_RSTMGR_STAT_FPGAWARMRST_SET_MSK    0x00000200
/* The mask used to clear the ALT_RSTMGR_STAT_FPGAWARMRST register field value. */
#define ALT_RSTMGR_STAT_FPGAWARMRST_CLR_MSK    0xfffffdff
/* The reset value of the ALT_RSTMGR_STAT_FPGAWARMRST register field. */
#define ALT_RSTMGR_STAT_FPGAWARMRST_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_FPGAWARMRST field value from a register. */
#define ALT_RSTMGR_STAT_FPGAWARMRST_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_RSTMGR_STAT_FPGAWARMRST register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_FPGAWARMRST_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Software Warm Reset - swwarmrst
 * 
 * Software wrote CTRL.SWWARMRSTREQ to 1 and triggered a hardware sequenced warm
 * reset
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_SWWARMRST register field. */
#define ALT_RSTMGR_STAT_SWWARMRST_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_SWWARMRST register field. */
#define ALT_RSTMGR_STAT_SWWARMRST_MSB        10
/* The width in bits of the ALT_RSTMGR_STAT_SWWARMRST register field. */
#define ALT_RSTMGR_STAT_SWWARMRST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_SWWARMRST register field value. */
#define ALT_RSTMGR_STAT_SWWARMRST_SET_MSK    0x00000400
/* The mask used to clear the ALT_RSTMGR_STAT_SWWARMRST register field value. */
#define ALT_RSTMGR_STAT_SWWARMRST_CLR_MSK    0xfffffbff
/* The reset value of the ALT_RSTMGR_STAT_SWWARMRST register field. */
#define ALT_RSTMGR_STAT_SWWARMRST_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_SWWARMRST field value from a register. */
#define ALT_RSTMGR_STAT_SWWARMRST_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_RSTMGR_STAT_SWWARMRST register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_SWWARMRST_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : MPU Watchdog 0 Warm Reset - mpuwd0rst
 * 
 * MPU Watchdog 0 triggered a hardware sequenced warm reset
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_MPUWD0RST register field. */
#define ALT_RSTMGR_STAT_MPUWD0RST_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_MPUWD0RST register field. */
#define ALT_RSTMGR_STAT_MPUWD0RST_MSB        12
/* The width in bits of the ALT_RSTMGR_STAT_MPUWD0RST register field. */
#define ALT_RSTMGR_STAT_MPUWD0RST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_MPUWD0RST register field value. */
#define ALT_RSTMGR_STAT_MPUWD0RST_SET_MSK    0x00001000
/* The mask used to clear the ALT_RSTMGR_STAT_MPUWD0RST register field value. */
#define ALT_RSTMGR_STAT_MPUWD0RST_CLR_MSK    0xffffefff
/* The reset value of the ALT_RSTMGR_STAT_MPUWD0RST register field. */
#define ALT_RSTMGR_STAT_MPUWD0RST_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_MPUWD0RST field value from a register. */
#define ALT_RSTMGR_STAT_MPUWD0RST_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_RSTMGR_STAT_MPUWD0RST register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_MPUWD0RST_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : MPU Watchdog 1 Warm Reset - mpuwd1rst
 * 
 * MPU Watchdog 1 triggered a hardware sequenced warm reset
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_MPUWD1RST register field. */
#define ALT_RSTMGR_STAT_MPUWD1RST_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_MPUWD1RST register field. */
#define ALT_RSTMGR_STAT_MPUWD1RST_MSB        13
/* The width in bits of the ALT_RSTMGR_STAT_MPUWD1RST register field. */
#define ALT_RSTMGR_STAT_MPUWD1RST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_MPUWD1RST register field value. */
#define ALT_RSTMGR_STAT_MPUWD1RST_SET_MSK    0x00002000
/* The mask used to clear the ALT_RSTMGR_STAT_MPUWD1RST register field value. */
#define ALT_RSTMGR_STAT_MPUWD1RST_CLR_MSK    0xffffdfff
/* The reset value of the ALT_RSTMGR_STAT_MPUWD1RST register field. */
#define ALT_RSTMGR_STAT_MPUWD1RST_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_MPUWD1RST field value from a register. */
#define ALT_RSTMGR_STAT_MPUWD1RST_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_RSTMGR_STAT_MPUWD1RST register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_MPUWD1RST_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : L4 Watchdog 0 Warm Reset - l4wd0rst
 * 
 * L4 Watchdog 0 triggered a hardware sequenced warm reset
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_L4WD0RST register field. */
#define ALT_RSTMGR_STAT_L4WD0RST_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_L4WD0RST register field. */
#define ALT_RSTMGR_STAT_L4WD0RST_MSB        14
/* The width in bits of the ALT_RSTMGR_STAT_L4WD0RST register field. */
#define ALT_RSTMGR_STAT_L4WD0RST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_L4WD0RST register field value. */
#define ALT_RSTMGR_STAT_L4WD0RST_SET_MSK    0x00004000
/* The mask used to clear the ALT_RSTMGR_STAT_L4WD0RST register field value. */
#define ALT_RSTMGR_STAT_L4WD0RST_CLR_MSK    0xffffbfff
/* The reset value of the ALT_RSTMGR_STAT_L4WD0RST register field. */
#define ALT_RSTMGR_STAT_L4WD0RST_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_L4WD0RST field value from a register. */
#define ALT_RSTMGR_STAT_L4WD0RST_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_RSTMGR_STAT_L4WD0RST register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_L4WD0RST_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : L4 Watchdog 1 Warm Reset - l4wd1rst
 * 
 * L4 Watchdog 1 triggered a hardware sequenced warm reset
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_L4WD1RST register field. */
#define ALT_RSTMGR_STAT_L4WD1RST_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_L4WD1RST register field. */
#define ALT_RSTMGR_STAT_L4WD1RST_MSB        15
/* The width in bits of the ALT_RSTMGR_STAT_L4WD1RST register field. */
#define ALT_RSTMGR_STAT_L4WD1RST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_L4WD1RST register field value. */
#define ALT_RSTMGR_STAT_L4WD1RST_SET_MSK    0x00008000
/* The mask used to clear the ALT_RSTMGR_STAT_L4WD1RST register field value. */
#define ALT_RSTMGR_STAT_L4WD1RST_CLR_MSK    0xffff7fff
/* The reset value of the ALT_RSTMGR_STAT_L4WD1RST register field. */
#define ALT_RSTMGR_STAT_L4WD1RST_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_L4WD1RST field value from a register. */
#define ALT_RSTMGR_STAT_L4WD1RST_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_RSTMGR_STAT_L4WD1RST register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_L4WD1RST_SET(value) (((value) << 15) & 0x00008000)

/*
 * Field : FPGA Core Debug Reset - fpgadbgrst
 * 
 * FPGA triggered debug reset (f2h_dbg_rst_req_n = 1)
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_FPGADBGRST register field. */
#define ALT_RSTMGR_STAT_FPGADBGRST_LSB        18
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_FPGADBGRST register field. */
#define ALT_RSTMGR_STAT_FPGADBGRST_MSB        18
/* The width in bits of the ALT_RSTMGR_STAT_FPGADBGRST register field. */
#define ALT_RSTMGR_STAT_FPGADBGRST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_FPGADBGRST register field value. */
#define ALT_RSTMGR_STAT_FPGADBGRST_SET_MSK    0x00040000
/* The mask used to clear the ALT_RSTMGR_STAT_FPGADBGRST register field value. */
#define ALT_RSTMGR_STAT_FPGADBGRST_CLR_MSK    0xfffbffff
/* The reset value of the ALT_RSTMGR_STAT_FPGADBGRST register field. */
#define ALT_RSTMGR_STAT_FPGADBGRST_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_FPGADBGRST field value from a register. */
#define ALT_RSTMGR_STAT_FPGADBGRST_GET(value) (((value) & 0x00040000) >> 18)
/* Produces a ALT_RSTMGR_STAT_FPGADBGRST register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_FPGADBGRST_SET(value) (((value) << 18) & 0x00040000)

/*
 * Field : DAP Debug Reset - cdbgreqrst
 * 
 * DAP triggered debug reset
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_CDBGREQRST register field. */
#define ALT_RSTMGR_STAT_CDBGREQRST_LSB        19
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_CDBGREQRST register field. */
#define ALT_RSTMGR_STAT_CDBGREQRST_MSB        19
/* The width in bits of the ALT_RSTMGR_STAT_CDBGREQRST register field. */
#define ALT_RSTMGR_STAT_CDBGREQRST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_CDBGREQRST register field value. */
#define ALT_RSTMGR_STAT_CDBGREQRST_SET_MSK    0x00080000
/* The mask used to clear the ALT_RSTMGR_STAT_CDBGREQRST register field value. */
#define ALT_RSTMGR_STAT_CDBGREQRST_CLR_MSK    0xfff7ffff
/* The reset value of the ALT_RSTMGR_STAT_CDBGREQRST register field. */
#define ALT_RSTMGR_STAT_CDBGREQRST_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_CDBGREQRST field value from a register. */
#define ALT_RSTMGR_STAT_CDBGREQRST_GET(value) (((value) & 0x00080000) >> 19)
/* Produces a ALT_RSTMGR_STAT_CDBGREQRST register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_CDBGREQRST_SET(value) (((value) << 19) & 0x00080000)

/*
 * Field : SDRAM Self-Refresh Timeout - sdrselfreftimeout
 * 
 * A 1 indicates that Reset Manager's request to the SDRAM Controller Subsystem to
 * put the SDRAM devices into self-refresh mode before starting a hardware
 * sequenced warm reset timed-out and the Reset Manager had to proceed with the
 * warm reset anyway.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_SDRSELFREFTMO register field. */
#define ALT_RSTMGR_STAT_SDRSELFREFTMO_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_SDRSELFREFTMO register field. */
#define ALT_RSTMGR_STAT_SDRSELFREFTMO_MSB        24
/* The width in bits of the ALT_RSTMGR_STAT_SDRSELFREFTMO register field. */
#define ALT_RSTMGR_STAT_SDRSELFREFTMO_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_SDRSELFREFTMO register field value. */
#define ALT_RSTMGR_STAT_SDRSELFREFTMO_SET_MSK    0x01000000
/* The mask used to clear the ALT_RSTMGR_STAT_SDRSELFREFTMO register field value. */
#define ALT_RSTMGR_STAT_SDRSELFREFTMO_CLR_MSK    0xfeffffff
/* The reset value of the ALT_RSTMGR_STAT_SDRSELFREFTMO register field. */
#define ALT_RSTMGR_STAT_SDRSELFREFTMO_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_SDRSELFREFTMO field value from a register. */
#define ALT_RSTMGR_STAT_SDRSELFREFTMO_GET(value) (((value) & 0x01000000) >> 24)
/* Produces a ALT_RSTMGR_STAT_SDRSELFREFTMO register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_SDRSELFREFTMO_SET(value) (((value) << 24) & 0x01000000)

/*
 * Field : FPGA manager handshake Timeout - fpgamgrhstimeout
 * 
 * A 1 indicates that Reset Manager's request to the FPGA manager to stop driving
 * configuration clock to FPGA CB before starting a hardware sequenced warm reset
 * timed-out and the Reset Manager had to proceed with the warm reset anyway.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_FPGAMGRHSTMO register field. */
#define ALT_RSTMGR_STAT_FPGAMGRHSTMO_LSB        25
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_FPGAMGRHSTMO register field. */
#define ALT_RSTMGR_STAT_FPGAMGRHSTMO_MSB        25
/* The width in bits of the ALT_RSTMGR_STAT_FPGAMGRHSTMO register field. */
#define ALT_RSTMGR_STAT_FPGAMGRHSTMO_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_FPGAMGRHSTMO register field value. */
#define ALT_RSTMGR_STAT_FPGAMGRHSTMO_SET_MSK    0x02000000
/* The mask used to clear the ALT_RSTMGR_STAT_FPGAMGRHSTMO register field value. */
#define ALT_RSTMGR_STAT_FPGAMGRHSTMO_CLR_MSK    0xfdffffff
/* The reset value of the ALT_RSTMGR_STAT_FPGAMGRHSTMO register field. */
#define ALT_RSTMGR_STAT_FPGAMGRHSTMO_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_FPGAMGRHSTMO field value from a register. */
#define ALT_RSTMGR_STAT_FPGAMGRHSTMO_GET(value) (((value) & 0x02000000) >> 25)
/* Produces a ALT_RSTMGR_STAT_FPGAMGRHSTMO register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_FPGAMGRHSTMO_SET(value) (((value) << 25) & 0x02000000)

/*
 * Field : SCAN manager handshake Timeout - scanhstimeout
 * 
 * A 1 indicates that Reset Manager's request to the SCAN manager to stop driving
 * JTAG clock to FPGA CB before starting a hardware sequenced warm reset timed-out
 * and the Reset Manager had to proceed with the warm reset anyway.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_SCANHSTMO register field. */
#define ALT_RSTMGR_STAT_SCANHSTMO_LSB        26
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_SCANHSTMO register field. */
#define ALT_RSTMGR_STAT_SCANHSTMO_MSB        26
/* The width in bits of the ALT_RSTMGR_STAT_SCANHSTMO register field. */
#define ALT_RSTMGR_STAT_SCANHSTMO_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_SCANHSTMO register field value. */
#define ALT_RSTMGR_STAT_SCANHSTMO_SET_MSK    0x04000000
/* The mask used to clear the ALT_RSTMGR_STAT_SCANHSTMO register field value. */
#define ALT_RSTMGR_STAT_SCANHSTMO_CLR_MSK    0xfbffffff
/* The reset value of the ALT_RSTMGR_STAT_SCANHSTMO register field. */
#define ALT_RSTMGR_STAT_SCANHSTMO_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_SCANHSTMO field value from a register. */
#define ALT_RSTMGR_STAT_SCANHSTMO_GET(value) (((value) & 0x04000000) >> 26)
/* Produces a ALT_RSTMGR_STAT_SCANHSTMO register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_SCANHSTMO_SET(value) (((value) << 26) & 0x04000000)

/*
 * Field : FPGA handshake Timeout - fpgahstimeout
 * 
 * A 1 indicates that Reset Manager's handshake request to FPGA before starting a
 * hardware sequenced warm reset timed-out and the Reset Manager had to proceed
 * with the warm reset anyway.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_FPGAHSTMO register field. */
#define ALT_RSTMGR_STAT_FPGAHSTMO_LSB        27
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_FPGAHSTMO register field. */
#define ALT_RSTMGR_STAT_FPGAHSTMO_MSB        27
/* The width in bits of the ALT_RSTMGR_STAT_FPGAHSTMO register field. */
#define ALT_RSTMGR_STAT_FPGAHSTMO_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_FPGAHSTMO register field value. */
#define ALT_RSTMGR_STAT_FPGAHSTMO_SET_MSK    0x08000000
/* The mask used to clear the ALT_RSTMGR_STAT_FPGAHSTMO register field value. */
#define ALT_RSTMGR_STAT_FPGAHSTMO_CLR_MSK    0xf7ffffff
/* The reset value of the ALT_RSTMGR_STAT_FPGAHSTMO register field. */
#define ALT_RSTMGR_STAT_FPGAHSTMO_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_FPGAHSTMO field value from a register. */
#define ALT_RSTMGR_STAT_FPGAHSTMO_GET(value) (((value) & 0x08000000) >> 27)
/* Produces a ALT_RSTMGR_STAT_FPGAHSTMO register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_FPGAHSTMO_SET(value) (((value) << 27) & 0x08000000)

/*
 * Field : ETR Stall Timeout - etrstalltimeout
 * 
 * A 1 indicates that Reset Manager's request to the ETR (Embedded Trace Router) to
 * stall its AXI master port before starting a hardware sequenced warm reset timed-
 * out and the Reset Manager had to proceed with the warm reset anyway.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_STAT_ETRSTALLTMO register field. */
#define ALT_RSTMGR_STAT_ETRSTALLTMO_LSB        28
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_STAT_ETRSTALLTMO register field. */
#define ALT_RSTMGR_STAT_ETRSTALLTMO_MSB        28
/* The width in bits of the ALT_RSTMGR_STAT_ETRSTALLTMO register field. */
#define ALT_RSTMGR_STAT_ETRSTALLTMO_WIDTH      1
/* The mask used to set the ALT_RSTMGR_STAT_ETRSTALLTMO register field value. */
#define ALT_RSTMGR_STAT_ETRSTALLTMO_SET_MSK    0x10000000
/* The mask used to clear the ALT_RSTMGR_STAT_ETRSTALLTMO register field value. */
#define ALT_RSTMGR_STAT_ETRSTALLTMO_CLR_MSK    0xefffffff
/* The reset value of the ALT_RSTMGR_STAT_ETRSTALLTMO register field. */
#define ALT_RSTMGR_STAT_ETRSTALLTMO_RESET      0x0
/* Extracts the ALT_RSTMGR_STAT_ETRSTALLTMO field value from a register. */
#define ALT_RSTMGR_STAT_ETRSTALLTMO_GET(value) (((value) & 0x10000000) >> 28)
/* Produces a ALT_RSTMGR_STAT_ETRSTALLTMO register field value suitable for setting the register. */
#define ALT_RSTMGR_STAT_ETRSTALLTMO_SET(value) (((value) << 28) & 0x10000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_RSTMGR_STAT.
 */
struct ALT_RSTMGR_STAT_s
{
    uint32_t  porvoltrst        :  1;  /* Power-On Voltage Detector Cold Reset */
    uint32_t  nporpinrst        :  1;  /* nPOR Pin Cold Reset */
    uint32_t  fpgacoldrst       :  1;  /* FPGA Core Cold Reset */
    uint32_t  configiocoldrst   :  1;  /* CONFIG_IO Cold Reset */
    uint32_t  swcoldrst         :  1;  /* Software Cold Reset */
    uint32_t                    :  3;  /* *UNDEFINED* */
    uint32_t  nrstpinrst        :  1;  /* nRST Pin Warm Reset */
    uint32_t  fpgawarmrst       :  1;  /* FPGA Core Warm Reset */
    uint32_t  swwarmrst         :  1;  /* Software Warm Reset */
    uint32_t                    :  1;  /* *UNDEFINED* */
    uint32_t  mpuwd0rst         :  1;  /* MPU Watchdog 0 Warm Reset */
    uint32_t  mpuwd1rst         :  1;  /* MPU Watchdog 1 Warm Reset */
    uint32_t  l4wd0rst          :  1;  /* L4 Watchdog 0 Warm Reset */
    uint32_t  l4wd1rst          :  1;  /* L4 Watchdog 1 Warm Reset */
    uint32_t                    :  2;  /* *UNDEFINED* */
    uint32_t  fpgadbgrst        :  1;  /* FPGA Core Debug Reset */
    uint32_t  cdbgreqrst        :  1;  /* DAP Debug Reset */
    uint32_t                    :  4;  /* *UNDEFINED* */
    uint32_t  sdrselfreftimeout :  1;  /* SDRAM Self-Refresh Timeout */
    uint32_t  fpgamgrhstimeout  :  1;  /* FPGA manager handshake Timeout */
    uint32_t  scanhstimeout     :  1;  /* SCAN manager handshake Timeout */
    uint32_t  fpgahstimeout     :  1;  /* FPGA handshake Timeout */
    uint32_t  etrstalltimeout   :  1;  /* ETR Stall Timeout */
    uint32_t                    :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_RSTMGR_STAT. */
typedef volatile struct ALT_RSTMGR_STAT_s  ALT_RSTMGR_STAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_RSTMGR_STAT register from the beginning of the component. */
#define ALT_RSTMGR_STAT_OFST        0x0

/*
 * Register : Control Register - ctrl
 * 
 * The CTRL register is used by software to control reset behavior.It includes
 * fields for software to initiate the cold and warm reset, enable hardware
 * handshake with other modules before warm reset, and perform software handshake.
 * The software handshake sequence must match the hardware sequence. Software
 * mustde-assert the handshake request after asserting warm reset and before de-
 * assert the warm reset.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset   | Description                                       
 * :--------|:-------|:--------|:---------------------------------------------------
 *  [0]     | RW     | 0x0     | Software Cold Reset Request                       
 *  [1]     | RW     | 0x0     | Software Warm Reset Request                       
 *  [3:2]   | ???    | 0x0     | *UNDEFINED*                                       
 *  [4]     | RW     | 0x0     | SDRAM Self-Refresh Enable                         
 *  [5]     | RW     | 0x0     | SDRAM Self-Refresh Request                        
 *  [6]     | R      | 0x0     | SDRAM Self-Refresh Acknowledge                    
 *  [7]     | ???    | 0x0     | *UNDEFINED*                                       
 *  [8]     | RW     | 0x0     | FPGA Manager Handshake Enable                     
 *  [9]     | RW     | 0x0     | FPGA Manager Handshake Request                    
 *  [10]    | R      | Unknown | FPGA Manager Handshake Acknowledge                
 *  [11]    | ???    | 0x0     | *UNDEFINED*                                       
 *  [12]    | RW     | 0x0     | SCAN Manager Handshake Enable                     
 *  [13]    | RW     | 0x0     | SCAN Manager Handshake Request                    
 *  [14]    | R      | Unknown | SCAN Manager Handshake Acknowledge                
 *  [15]    | ???    | 0x0     | *UNDEFINED*                                       
 *  [16]    | RW     | 0x0     | FPGA Handshake Enable                             
 *  [17]    | RW     | 0x0     | FPGA Handshake Request                            
 *  [18]    | R      | Unknown | FPGA Handshake Acknowledge                        
 *  [19]    | ???    | 0x0     | *UNDEFINED*                                       
 *  [20]    | RW     | 0x1     | ETR (Embedded Trace Router) Stall Enable          
 *  [21]    | RW     | 0x0     | ETR (Embedded Trace Router) Stall Request         
 *  [22]    | R      | 0x0     | ETR (Embedded Trace Router) Stall Acknowledge     
 *  [23]    | RW     | 0x0     | ETR (Embedded Trace Router) Stall After Warm Reset
 *  [31:24] | ???    | 0x0     | *UNDEFINED*                                       
 * 
 */
/*
 * Field : Software Cold Reset Request - swcoldrstreq
 * 
 * This is a one-shot bit written by software to 1 to trigger a cold reset. It
 * always reads the value 0.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_SWCOLDRSTREQ register field. */
#define ALT_RSTMGR_CTL_SWCOLDRSTREQ_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_SWCOLDRSTREQ register field. */
#define ALT_RSTMGR_CTL_SWCOLDRSTREQ_MSB        0
/* The width in bits of the ALT_RSTMGR_CTL_SWCOLDRSTREQ register field. */
#define ALT_RSTMGR_CTL_SWCOLDRSTREQ_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_SWCOLDRSTREQ register field value. */
#define ALT_RSTMGR_CTL_SWCOLDRSTREQ_SET_MSK    0x00000001
/* The mask used to clear the ALT_RSTMGR_CTL_SWCOLDRSTREQ register field value. */
#define ALT_RSTMGR_CTL_SWCOLDRSTREQ_CLR_MSK    0xfffffffe
/* The reset value of the ALT_RSTMGR_CTL_SWCOLDRSTREQ register field. */
#define ALT_RSTMGR_CTL_SWCOLDRSTREQ_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_SWCOLDRSTREQ field value from a register. */
#define ALT_RSTMGR_CTL_SWCOLDRSTREQ_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_RSTMGR_CTL_SWCOLDRSTREQ register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_SWCOLDRSTREQ_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Software Warm Reset Request - swwarmrstreq
 * 
 * This is a one-shot bit written by software to 1 to trigger a hardware sequenced
 * warm reset. It always reads the value 0.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_SWWARMRSTREQ register field. */
#define ALT_RSTMGR_CTL_SWWARMRSTREQ_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_SWWARMRSTREQ register field. */
#define ALT_RSTMGR_CTL_SWWARMRSTREQ_MSB        1
/* The width in bits of the ALT_RSTMGR_CTL_SWWARMRSTREQ register field. */
#define ALT_RSTMGR_CTL_SWWARMRSTREQ_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_SWWARMRSTREQ register field value. */
#define ALT_RSTMGR_CTL_SWWARMRSTREQ_SET_MSK    0x00000002
/* The mask used to clear the ALT_RSTMGR_CTL_SWWARMRSTREQ register field value. */
#define ALT_RSTMGR_CTL_SWWARMRSTREQ_CLR_MSK    0xfffffffd
/* The reset value of the ALT_RSTMGR_CTL_SWWARMRSTREQ register field. */
#define ALT_RSTMGR_CTL_SWWARMRSTREQ_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_SWWARMRSTREQ field value from a register. */
#define ALT_RSTMGR_CTL_SWWARMRSTREQ_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_RSTMGR_CTL_SWWARMRSTREQ register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_SWWARMRSTREQ_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : SDRAM Self-Refresh Enable - sdrselfrefen
 * 
 * This field controls whether the contents of SDRAM devices survive a hardware
 * sequenced warm reset. If set to 1, the Reset Manager makes a request to the
 * SDRAM Controller Subsystem to put the SDRAM devices into self-refresh mode
 * before asserting warm reset signals. However, if SDRAM is already in warm reset,
 * Handshake with SDRAM is not performed.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_SDRSELFREFEN register field. */
#define ALT_RSTMGR_CTL_SDRSELFREFEN_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_SDRSELFREFEN register field. */
#define ALT_RSTMGR_CTL_SDRSELFREFEN_MSB        4
/* The width in bits of the ALT_RSTMGR_CTL_SDRSELFREFEN register field. */
#define ALT_RSTMGR_CTL_SDRSELFREFEN_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_SDRSELFREFEN register field value. */
#define ALT_RSTMGR_CTL_SDRSELFREFEN_SET_MSK    0x00000010
/* The mask used to clear the ALT_RSTMGR_CTL_SDRSELFREFEN register field value. */
#define ALT_RSTMGR_CTL_SDRSELFREFEN_CLR_MSK    0xffffffef
/* The reset value of the ALT_RSTMGR_CTL_SDRSELFREFEN register field. */
#define ALT_RSTMGR_CTL_SDRSELFREFEN_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_SDRSELFREFEN field value from a register. */
#define ALT_RSTMGR_CTL_SDRSELFREFEN_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_RSTMGR_CTL_SDRSELFREFEN register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_SDRSELFREFEN_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : SDRAM Self-Refresh Request - sdrselfrefreq
 * 
 * Software writes this field 1 to request to the SDRAM Controller Subsystem that
 * it puts the SDRAM devices into self-refresh mode. This is done to preserve SDRAM
 * contents across a software warm reset.
 * 
 * Software waits for the SDRSELFREFACK to be 1 and then writes this field to 0.
 * Note that it is possible for the SDRAM Controller Subsystem to never assert
 * SDRSELFREFACK so software should timeout if SDRSELFREFACK is never asserted.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_SDRSELFREFREQ register field. */
#define ALT_RSTMGR_CTL_SDRSELFREFREQ_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_SDRSELFREFREQ register field. */
#define ALT_RSTMGR_CTL_SDRSELFREFREQ_MSB        5
/* The width in bits of the ALT_RSTMGR_CTL_SDRSELFREFREQ register field. */
#define ALT_RSTMGR_CTL_SDRSELFREFREQ_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_SDRSELFREFREQ register field value. */
#define ALT_RSTMGR_CTL_SDRSELFREFREQ_SET_MSK    0x00000020
/* The mask used to clear the ALT_RSTMGR_CTL_SDRSELFREFREQ register field value. */
#define ALT_RSTMGR_CTL_SDRSELFREFREQ_CLR_MSK    0xffffffdf
/* The reset value of the ALT_RSTMGR_CTL_SDRSELFREFREQ register field. */
#define ALT_RSTMGR_CTL_SDRSELFREFREQ_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_SDRSELFREFREQ field value from a register. */
#define ALT_RSTMGR_CTL_SDRSELFREFREQ_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_RSTMGR_CTL_SDRSELFREFREQ register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_SDRSELFREFREQ_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : SDRAM Self-Refresh Acknowledge - sdrselfreqack
 * 
 * This is the acknowlege for a SDRAM self-refresh mode request initiated by the
 * SDRSELFREFREQ field.  A 1 indicates that the SDRAM Controller Subsystem has put
 * the SDRAM devices into self-refresh mode.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_SDRSELFREQACK register field. */
#define ALT_RSTMGR_CTL_SDRSELFREQACK_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_SDRSELFREQACK register field. */
#define ALT_RSTMGR_CTL_SDRSELFREQACK_MSB        6
/* The width in bits of the ALT_RSTMGR_CTL_SDRSELFREQACK register field. */
#define ALT_RSTMGR_CTL_SDRSELFREQACK_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_SDRSELFREQACK register field value. */
#define ALT_RSTMGR_CTL_SDRSELFREQACK_SET_MSK    0x00000040
/* The mask used to clear the ALT_RSTMGR_CTL_SDRSELFREQACK register field value. */
#define ALT_RSTMGR_CTL_SDRSELFREQACK_CLR_MSK    0xffffffbf
/* The reset value of the ALT_RSTMGR_CTL_SDRSELFREQACK register field. */
#define ALT_RSTMGR_CTL_SDRSELFREQACK_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_SDRSELFREQACK field value from a register. */
#define ALT_RSTMGR_CTL_SDRSELFREQACK_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_RSTMGR_CTL_SDRSELFREQACK register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_SDRSELFREQACK_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : FPGA Manager Handshake Enable - fpgamgrhsen
 * 
 * Enables a handshake between the Reset Manager and FPGA Manager before a warm
 * reset. The handshake is used to warn the FPGA Manager that a warm reset it
 * coming so it can prepare for it. When the FPGA Manager receives a warm reset
 * handshake, the FPGA Manager drives its output clock to a quiescent state to
 * avoid glitches.
 * 
 * If set to 1, the  Manager makes a request to the FPGA Managerbefore asserting
 * warm reset signals. However if the FPGA Manager is already in warm reset, the
 * handshake is skipped.
 * 
 * If set to 0, the handshake is skipped.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_FPGAMGRHSEN register field. */
#define ALT_RSTMGR_CTL_FPGAMGRHSEN_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_FPGAMGRHSEN register field. */
#define ALT_RSTMGR_CTL_FPGAMGRHSEN_MSB        8
/* The width in bits of the ALT_RSTMGR_CTL_FPGAMGRHSEN register field. */
#define ALT_RSTMGR_CTL_FPGAMGRHSEN_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_FPGAMGRHSEN register field value. */
#define ALT_RSTMGR_CTL_FPGAMGRHSEN_SET_MSK    0x00000100
/* The mask used to clear the ALT_RSTMGR_CTL_FPGAMGRHSEN register field value. */
#define ALT_RSTMGR_CTL_FPGAMGRHSEN_CLR_MSK    0xfffffeff
/* The reset value of the ALT_RSTMGR_CTL_FPGAMGRHSEN register field. */
#define ALT_RSTMGR_CTL_FPGAMGRHSEN_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_FPGAMGRHSEN field value from a register. */
#define ALT_RSTMGR_CTL_FPGAMGRHSEN_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_RSTMGR_CTL_FPGAMGRHSEN register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_FPGAMGRHSEN_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : FPGA Manager Handshake Request - fpgamgrhsreq
 * 
 * Software writes this field 1 to request to the FPGA Manager to idle its output
 * clock.
 * 
 * Software waits for the FPGAMGRHSACK to be 1 and then writes this field to 0.
 * Note that it is possible for the FPGA Manager to never assert FPGAMGRHSACK so
 * software should timeout in this case.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_FPGAMGRHSREQ register field. */
#define ALT_RSTMGR_CTL_FPGAMGRHSREQ_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_FPGAMGRHSREQ register field. */
#define ALT_RSTMGR_CTL_FPGAMGRHSREQ_MSB        9
/* The width in bits of the ALT_RSTMGR_CTL_FPGAMGRHSREQ register field. */
#define ALT_RSTMGR_CTL_FPGAMGRHSREQ_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_FPGAMGRHSREQ register field value. */
#define ALT_RSTMGR_CTL_FPGAMGRHSREQ_SET_MSK    0x00000200
/* The mask used to clear the ALT_RSTMGR_CTL_FPGAMGRHSREQ register field value. */
#define ALT_RSTMGR_CTL_FPGAMGRHSREQ_CLR_MSK    0xfffffdff
/* The reset value of the ALT_RSTMGR_CTL_FPGAMGRHSREQ register field. */
#define ALT_RSTMGR_CTL_FPGAMGRHSREQ_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_FPGAMGRHSREQ field value from a register. */
#define ALT_RSTMGR_CTL_FPGAMGRHSREQ_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_RSTMGR_CTL_FPGAMGRHSREQ register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_FPGAMGRHSREQ_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : FPGA Manager Handshake Acknowledge - fpgamgrhsack
 * 
 * This is the acknowlege (high active) that the FPGA manager has successfully
 * idled its output clock.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_FPGAMGRHSACK register field. */
#define ALT_RSTMGR_CTL_FPGAMGRHSACK_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_FPGAMGRHSACK register field. */
#define ALT_RSTMGR_CTL_FPGAMGRHSACK_MSB        10
/* The width in bits of the ALT_RSTMGR_CTL_FPGAMGRHSACK register field. */
#define ALT_RSTMGR_CTL_FPGAMGRHSACK_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_FPGAMGRHSACK register field value. */
#define ALT_RSTMGR_CTL_FPGAMGRHSACK_SET_MSK    0x00000400
/* The mask used to clear the ALT_RSTMGR_CTL_FPGAMGRHSACK register field value. */
#define ALT_RSTMGR_CTL_FPGAMGRHSACK_CLR_MSK    0xfffffbff
/* The reset value of the ALT_RSTMGR_CTL_FPGAMGRHSACK register field is UNKNOWN. */
#define ALT_RSTMGR_CTL_FPGAMGRHSACK_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_FPGAMGRHSACK field value from a register. */
#define ALT_RSTMGR_CTL_FPGAMGRHSACK_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_RSTMGR_CTL_FPGAMGRHSACK register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_FPGAMGRHSACK_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : SCAN Manager Handshake Enable - scanmgrhsen
 * 
 * Enables a handshake between the Reset Manager and Scan Manager before a warm
 * reset. The handshake is used to warn the Scan Manager that a warm reset it
 * coming so it can prepare for it. When the Scan Manager receives a warm reset
 * handshake, the Scan Manager drives its output clocks to a quiescent state to
 * avoid glitches.
 * 
 * If set to 1, the Reset Manager makes a request to the Scan Managerbefore
 * asserting warm reset signals. However if the Scan Manager is already in warm
 * reset, the handshake is skipped.
 * 
 * If set to 0, the handshake is skipped.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_SCANMGRHSEN register field. */
#define ALT_RSTMGR_CTL_SCANMGRHSEN_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_SCANMGRHSEN register field. */
#define ALT_RSTMGR_CTL_SCANMGRHSEN_MSB        12
/* The width in bits of the ALT_RSTMGR_CTL_SCANMGRHSEN register field. */
#define ALT_RSTMGR_CTL_SCANMGRHSEN_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_SCANMGRHSEN register field value. */
#define ALT_RSTMGR_CTL_SCANMGRHSEN_SET_MSK    0x00001000
/* The mask used to clear the ALT_RSTMGR_CTL_SCANMGRHSEN register field value. */
#define ALT_RSTMGR_CTL_SCANMGRHSEN_CLR_MSK    0xffffefff
/* The reset value of the ALT_RSTMGR_CTL_SCANMGRHSEN register field. */
#define ALT_RSTMGR_CTL_SCANMGRHSEN_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_SCANMGRHSEN field value from a register. */
#define ALT_RSTMGR_CTL_SCANMGRHSEN_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_RSTMGR_CTL_SCANMGRHSEN register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_SCANMGRHSEN_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : SCAN Manager Handshake Request - scanmgrhsreq
 * 
 * Software writes this field 1 to request to the SCAN manager to idle its output
 * clocks.
 * 
 * Software waits for the SCANMGRHSACK to be 1 and then writes this field to 0.
 * Note that it is possible for the Scan Manager to never assert SCANMGRHSACK (e.g.
 * its input clock is disabled) so software should timeout in this case.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_SCANMGRHSREQ register field. */
#define ALT_RSTMGR_CTL_SCANMGRHSREQ_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_SCANMGRHSREQ register field. */
#define ALT_RSTMGR_CTL_SCANMGRHSREQ_MSB        13
/* The width in bits of the ALT_RSTMGR_CTL_SCANMGRHSREQ register field. */
#define ALT_RSTMGR_CTL_SCANMGRHSREQ_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_SCANMGRHSREQ register field value. */
#define ALT_RSTMGR_CTL_SCANMGRHSREQ_SET_MSK    0x00002000
/* The mask used to clear the ALT_RSTMGR_CTL_SCANMGRHSREQ register field value. */
#define ALT_RSTMGR_CTL_SCANMGRHSREQ_CLR_MSK    0xffffdfff
/* The reset value of the ALT_RSTMGR_CTL_SCANMGRHSREQ register field. */
#define ALT_RSTMGR_CTL_SCANMGRHSREQ_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_SCANMGRHSREQ field value from a register. */
#define ALT_RSTMGR_CTL_SCANMGRHSREQ_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_RSTMGR_CTL_SCANMGRHSREQ register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_SCANMGRHSREQ_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : SCAN Manager Handshake Acknowledge - scanmgrhsack
 * 
 * This is the acknowlege (high active) that the SCAN manager has   successfully
 * idled its output clocks.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_SCANMGRHSACK register field. */
#define ALT_RSTMGR_CTL_SCANMGRHSACK_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_SCANMGRHSACK register field. */
#define ALT_RSTMGR_CTL_SCANMGRHSACK_MSB        14
/* The width in bits of the ALT_RSTMGR_CTL_SCANMGRHSACK register field. */
#define ALT_RSTMGR_CTL_SCANMGRHSACK_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_SCANMGRHSACK register field value. */
#define ALT_RSTMGR_CTL_SCANMGRHSACK_SET_MSK    0x00004000
/* The mask used to clear the ALT_RSTMGR_CTL_SCANMGRHSACK register field value. */
#define ALT_RSTMGR_CTL_SCANMGRHSACK_CLR_MSK    0xffffbfff
/* The reset value of the ALT_RSTMGR_CTL_SCANMGRHSACK register field is UNKNOWN. */
#define ALT_RSTMGR_CTL_SCANMGRHSACK_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_SCANMGRHSACK field value from a register. */
#define ALT_RSTMGR_CTL_SCANMGRHSACK_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_RSTMGR_CTL_SCANMGRHSACK register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_SCANMGRHSACK_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : FPGA Handshake Enable - fpgahsen
 * 
 * This field controls whether to perform handshake with FPGA before asserting warm
 * reset.
 * 
 * If set to 1, the Reset Manager makes a request to the FPGAbefore asserting warm
 * reset signals. However if FPGA is already in warm reset state, the handshake is
 * not performed.
 * 
 * If set to 0, the handshake is not performed
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_FPGAHSEN register field. */
#define ALT_RSTMGR_CTL_FPGAHSEN_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_FPGAHSEN register field. */
#define ALT_RSTMGR_CTL_FPGAHSEN_MSB        16
/* The width in bits of the ALT_RSTMGR_CTL_FPGAHSEN register field. */
#define ALT_RSTMGR_CTL_FPGAHSEN_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_FPGAHSEN register field value. */
#define ALT_RSTMGR_CTL_FPGAHSEN_SET_MSK    0x00010000
/* The mask used to clear the ALT_RSTMGR_CTL_FPGAHSEN register field value. */
#define ALT_RSTMGR_CTL_FPGAHSEN_CLR_MSK    0xfffeffff
/* The reset value of the ALT_RSTMGR_CTL_FPGAHSEN register field. */
#define ALT_RSTMGR_CTL_FPGAHSEN_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_FPGAHSEN field value from a register. */
#define ALT_RSTMGR_CTL_FPGAHSEN_GET(value) (((value) & 0x00010000) >> 16)
/* Produces a ALT_RSTMGR_CTL_FPGAHSEN register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_FPGAHSEN_SET(value) (((value) << 16) & 0x00010000)

/*
 * Field : FPGA Handshake Request - fpgahsreq
 * 
 * Software writes this field 1 to initiate handshake  request to FPGA .
 * 
 * Software waits for the FPGAHSACK to be active and then writes this field to 0.
 * Note that it is possible for the FPGA to never assert FPGAHSACK so software
 * should timeout in this case.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_FPGAHSREQ register field. */
#define ALT_RSTMGR_CTL_FPGAHSREQ_LSB        17
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_FPGAHSREQ register field. */
#define ALT_RSTMGR_CTL_FPGAHSREQ_MSB        17
/* The width in bits of the ALT_RSTMGR_CTL_FPGAHSREQ register field. */
#define ALT_RSTMGR_CTL_FPGAHSREQ_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_FPGAHSREQ register field value. */
#define ALT_RSTMGR_CTL_FPGAHSREQ_SET_MSK    0x00020000
/* The mask used to clear the ALT_RSTMGR_CTL_FPGAHSREQ register field value. */
#define ALT_RSTMGR_CTL_FPGAHSREQ_CLR_MSK    0xfffdffff
/* The reset value of the ALT_RSTMGR_CTL_FPGAHSREQ register field. */
#define ALT_RSTMGR_CTL_FPGAHSREQ_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_FPGAHSREQ field value from a register. */
#define ALT_RSTMGR_CTL_FPGAHSREQ_GET(value) (((value) & 0x00020000) >> 17)
/* Produces a ALT_RSTMGR_CTL_FPGAHSREQ register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_FPGAHSREQ_SET(value) (((value) << 17) & 0x00020000)

/*
 * Field : FPGA Handshake Acknowledge - fpgahsack
 * 
 * This is the acknowlege (high active) that the FPGA handshake   acknowledge has
 * been received by Reset Manager.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_FPGAHSACK register field. */
#define ALT_RSTMGR_CTL_FPGAHSACK_LSB        18
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_FPGAHSACK register field. */
#define ALT_RSTMGR_CTL_FPGAHSACK_MSB        18
/* The width in bits of the ALT_RSTMGR_CTL_FPGAHSACK register field. */
#define ALT_RSTMGR_CTL_FPGAHSACK_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_FPGAHSACK register field value. */
#define ALT_RSTMGR_CTL_FPGAHSACK_SET_MSK    0x00040000
/* The mask used to clear the ALT_RSTMGR_CTL_FPGAHSACK register field value. */
#define ALT_RSTMGR_CTL_FPGAHSACK_CLR_MSK    0xfffbffff
/* The reset value of the ALT_RSTMGR_CTL_FPGAHSACK register field is UNKNOWN. */
#define ALT_RSTMGR_CTL_FPGAHSACK_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_FPGAHSACK field value from a register. */
#define ALT_RSTMGR_CTL_FPGAHSACK_GET(value) (((value) & 0x00040000) >> 18)
/* Produces a ALT_RSTMGR_CTL_FPGAHSACK register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_FPGAHSACK_SET(value) (((value) << 18) & 0x00040000)

/*
 * Field : ETR (Embedded Trace Router) Stall Enable - etrstallen
 * 
 * This field controls whether the ETR is requested to idle its AXI master
 * interface (i.e. finish outstanding transactions and not initiate any more) to
 * the L3 Interconnect before a warm or debug reset. If set to 1, the Reset Manager
 * makes a request to the ETR to stall its AXI master and waits for it to finish
 * any outstanding AXI transactions before a warm reset of the L3 Interconnect or a
 * debug reset of the ETR. This stalling is required because the debug logic
 * (including the ETR) is reset on a debug reset and the ETR AXI master is
 * connected to the L3 Interconnect which is reset on a warm reset and these resets
 * can happen independently.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_ETRSTALLEN register field. */
#define ALT_RSTMGR_CTL_ETRSTALLEN_LSB        20
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_ETRSTALLEN register field. */
#define ALT_RSTMGR_CTL_ETRSTALLEN_MSB        20
/* The width in bits of the ALT_RSTMGR_CTL_ETRSTALLEN register field. */
#define ALT_RSTMGR_CTL_ETRSTALLEN_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_ETRSTALLEN register field value. */
#define ALT_RSTMGR_CTL_ETRSTALLEN_SET_MSK    0x00100000
/* The mask used to clear the ALT_RSTMGR_CTL_ETRSTALLEN register field value. */
#define ALT_RSTMGR_CTL_ETRSTALLEN_CLR_MSK    0xffefffff
/* The reset value of the ALT_RSTMGR_CTL_ETRSTALLEN register field. */
#define ALT_RSTMGR_CTL_ETRSTALLEN_RESET      0x1
/* Extracts the ALT_RSTMGR_CTL_ETRSTALLEN field value from a register. */
#define ALT_RSTMGR_CTL_ETRSTALLEN_GET(value) (((value) & 0x00100000) >> 20)
/* Produces a ALT_RSTMGR_CTL_ETRSTALLEN register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_ETRSTALLEN_SET(value) (((value) << 20) & 0x00100000)

/*
 * Field : ETR (Embedded Trace Router) Stall Request - etrstallreq
 * 
 * Software writes this field 1 to request to the ETR that it stalls its AXI master
 * to the L3 Interconnect.
 * 
 * Software waits for the ETRSTALLACK to be 1 and then writes this field to 0.
 * Note that it is possible for the ETR to never assert ETRSTALLACK so software
 * should timeout if ETRSTALLACK is never asserted.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_ETRSTALLREQ register field. */
#define ALT_RSTMGR_CTL_ETRSTALLREQ_LSB        21
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_ETRSTALLREQ register field. */
#define ALT_RSTMGR_CTL_ETRSTALLREQ_MSB        21
/* The width in bits of the ALT_RSTMGR_CTL_ETRSTALLREQ register field. */
#define ALT_RSTMGR_CTL_ETRSTALLREQ_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_ETRSTALLREQ register field value. */
#define ALT_RSTMGR_CTL_ETRSTALLREQ_SET_MSK    0x00200000
/* The mask used to clear the ALT_RSTMGR_CTL_ETRSTALLREQ register field value. */
#define ALT_RSTMGR_CTL_ETRSTALLREQ_CLR_MSK    0xffdfffff
/* The reset value of the ALT_RSTMGR_CTL_ETRSTALLREQ register field. */
#define ALT_RSTMGR_CTL_ETRSTALLREQ_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_ETRSTALLREQ field value from a register. */
#define ALT_RSTMGR_CTL_ETRSTALLREQ_GET(value) (((value) & 0x00200000) >> 21)
/* Produces a ALT_RSTMGR_CTL_ETRSTALLREQ register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_ETRSTALLREQ_SET(value) (((value) << 21) & 0x00200000)

/*
 * Field : ETR (Embedded Trace Router) Stall Acknowledge - etrstallack
 * 
 * This is the acknowlege for a ETR AXI master stall initiated by the ETRSTALLREQ
 * field.  A 1 indicates that the ETR has stalled its AXI master
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_ETRSTALLACK register field. */
#define ALT_RSTMGR_CTL_ETRSTALLACK_LSB        22
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_ETRSTALLACK register field. */
#define ALT_RSTMGR_CTL_ETRSTALLACK_MSB        22
/* The width in bits of the ALT_RSTMGR_CTL_ETRSTALLACK register field. */
#define ALT_RSTMGR_CTL_ETRSTALLACK_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_ETRSTALLACK register field value. */
#define ALT_RSTMGR_CTL_ETRSTALLACK_SET_MSK    0x00400000
/* The mask used to clear the ALT_RSTMGR_CTL_ETRSTALLACK register field value. */
#define ALT_RSTMGR_CTL_ETRSTALLACK_CLR_MSK    0xffbfffff
/* The reset value of the ALT_RSTMGR_CTL_ETRSTALLACK register field. */
#define ALT_RSTMGR_CTL_ETRSTALLACK_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_ETRSTALLACK field value from a register. */
#define ALT_RSTMGR_CTL_ETRSTALLACK_GET(value) (((value) & 0x00400000) >> 22)
/* Produces a ALT_RSTMGR_CTL_ETRSTALLACK register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_ETRSTALLACK_SET(value) (((value) << 22) & 0x00400000)

/*
 * Field : ETR (Embedded Trace Router) Stall After Warm Reset - etrstallwarmrst
 * 
 * If a warm reset occurs and ETRSTALLEN is 1, hardware sets this bit to 1 to
 * indicate that the stall of the ETR AXI master is pending. Hardware leaves the
 * ETR stalled until software clears this field by writing it with 1. Software must
 * only clear this field when it is ready to have the ETR AXI master start making
 * AXI requests to write trace data.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_CTL_ETRSTALLWARMRST register field. */
#define ALT_RSTMGR_CTL_ETRSTALLWARMRST_LSB        23
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_CTL_ETRSTALLWARMRST register field. */
#define ALT_RSTMGR_CTL_ETRSTALLWARMRST_MSB        23
/* The width in bits of the ALT_RSTMGR_CTL_ETRSTALLWARMRST register field. */
#define ALT_RSTMGR_CTL_ETRSTALLWARMRST_WIDTH      1
/* The mask used to set the ALT_RSTMGR_CTL_ETRSTALLWARMRST register field value. */
#define ALT_RSTMGR_CTL_ETRSTALLWARMRST_SET_MSK    0x00800000
/* The mask used to clear the ALT_RSTMGR_CTL_ETRSTALLWARMRST register field value. */
#define ALT_RSTMGR_CTL_ETRSTALLWARMRST_CLR_MSK    0xff7fffff
/* The reset value of the ALT_RSTMGR_CTL_ETRSTALLWARMRST register field. */
#define ALT_RSTMGR_CTL_ETRSTALLWARMRST_RESET      0x0
/* Extracts the ALT_RSTMGR_CTL_ETRSTALLWARMRST field value from a register. */
#define ALT_RSTMGR_CTL_ETRSTALLWARMRST_GET(value) (((value) & 0x00800000) >> 23)
/* Produces a ALT_RSTMGR_CTL_ETRSTALLWARMRST register field value suitable for setting the register. */
#define ALT_RSTMGR_CTL_ETRSTALLWARMRST_SET(value) (((value) << 23) & 0x00800000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_RSTMGR_CTL.
 */
struct ALT_RSTMGR_CTL_s
{
    uint32_t        swcoldrstreq    :  1;  /* Software Cold Reset Request */
    uint32_t        swwarmrstreq    :  1;  /* Software Warm Reset Request */
    uint32_t                        :  2;  /* *UNDEFINED* */
    uint32_t        sdrselfrefen    :  1;  /* SDRAM Self-Refresh Enable */
    uint32_t        sdrselfrefreq   :  1;  /* SDRAM Self-Refresh Request */
    const uint32_t  sdrselfreqack   :  1;  /* SDRAM Self-Refresh Acknowledge */
    uint32_t                        :  1;  /* *UNDEFINED* */
    uint32_t        fpgamgrhsen     :  1;  /* FPGA Manager Handshake Enable */
    uint32_t        fpgamgrhsreq    :  1;  /* FPGA Manager Handshake Request */
    const uint32_t  fpgamgrhsack    :  1;  /* FPGA Manager Handshake Acknowledge */
    uint32_t                        :  1;  /* *UNDEFINED* */
    uint32_t        scanmgrhsen     :  1;  /* SCAN Manager Handshake Enable */
    uint32_t        scanmgrhsreq    :  1;  /* SCAN Manager Handshake Request */
    const uint32_t  scanmgrhsack    :  1;  /* SCAN Manager Handshake Acknowledge */
    uint32_t                        :  1;  /* *UNDEFINED* */
    uint32_t        fpgahsen        :  1;  /* FPGA Handshake Enable */
    uint32_t        fpgahsreq       :  1;  /* FPGA Handshake Request */
    const uint32_t  fpgahsack       :  1;  /* FPGA Handshake Acknowledge */
    uint32_t                        :  1;  /* *UNDEFINED* */
    uint32_t        etrstallen      :  1;  /* ETR (Embedded Trace Router) Stall Enable */
    uint32_t        etrstallreq     :  1;  /* ETR (Embedded Trace Router) Stall Request */
    const uint32_t  etrstallack     :  1;  /* ETR (Embedded Trace Router) Stall Acknowledge */
    uint32_t        etrstallwarmrst :  1;  /* ETR (Embedded Trace Router) Stall After Warm Reset */
    uint32_t                        :  8;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_RSTMGR_CTL. */
typedef volatile struct ALT_RSTMGR_CTL_s  ALT_RSTMGR_CTL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_RSTMGR_CTL register from the beginning of the component. */
#define ALT_RSTMGR_CTL_OFST        0x4

/*
 * Register : Reset Cycles Count Register - counts
 * 
 * The COUNTS register is used by software to control reset behavior.It includes
 * fields for software to control the behavior of the warm reset and nRST pin.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                   
 * :--------|:-------|:------|:-------------------------------
 *  [7:0]   | RW     | 0x80  | Warm reset release delay count
 *  [27:8]  | RW     | 0x800 | nRST Pin Count                
 *  [31:28] | ???    | 0x0   | *UNDEFINED*                   
 * 
 */
/*
 * Field : Warm reset release delay count - warmrstcycles
 * 
 * On a warm reset, the Reset Manager releases the reset to the Clock Manager, and
 * then waits for the number of cycles specified in this register before releasing
 * the rest of the hardware controlled resets.  Value must be greater than 16.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_COUNTS_WARMRSTCYCLES register field. */
#define ALT_RSTMGR_COUNTS_WARMRSTCYCLES_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_COUNTS_WARMRSTCYCLES register field. */
#define ALT_RSTMGR_COUNTS_WARMRSTCYCLES_MSB        7
/* The width in bits of the ALT_RSTMGR_COUNTS_WARMRSTCYCLES register field. */
#define ALT_RSTMGR_COUNTS_WARMRSTCYCLES_WIDTH      8
/* The mask used to set the ALT_RSTMGR_COUNTS_WARMRSTCYCLES register field value. */
#define ALT_RSTMGR_COUNTS_WARMRSTCYCLES_SET_MSK    0x000000ff
/* The mask used to clear the ALT_RSTMGR_COUNTS_WARMRSTCYCLES register field value. */
#define ALT_RSTMGR_COUNTS_WARMRSTCYCLES_CLR_MSK    0xffffff00
/* The reset value of the ALT_RSTMGR_COUNTS_WARMRSTCYCLES register field. */
#define ALT_RSTMGR_COUNTS_WARMRSTCYCLES_RESET      0x80
/* Extracts the ALT_RSTMGR_COUNTS_WARMRSTCYCLES field value from a register. */
#define ALT_RSTMGR_COUNTS_WARMRSTCYCLES_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_RSTMGR_COUNTS_WARMRSTCYCLES register field value suitable for setting the register. */
#define ALT_RSTMGR_COUNTS_WARMRSTCYCLES_SET(value) (((value) << 0) & 0x000000ff)

/*
 * Field : nRST Pin Count - nrstcnt
 * 
 * The Reset Manager pulls down the nRST pin on a warm reset for the number of
 * cycles specified in this register. A value of 0x0 prevents the Reset Manager
 * from pulling down the nRST pin.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_COUNTS_NRSTCNT register field. */
#define ALT_RSTMGR_COUNTS_NRSTCNT_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_COUNTS_NRSTCNT register field. */
#define ALT_RSTMGR_COUNTS_NRSTCNT_MSB        27
/* The width in bits of the ALT_RSTMGR_COUNTS_NRSTCNT register field. */
#define ALT_RSTMGR_COUNTS_NRSTCNT_WIDTH      20
/* The mask used to set the ALT_RSTMGR_COUNTS_NRSTCNT register field value. */
#define ALT_RSTMGR_COUNTS_NRSTCNT_SET_MSK    0x0fffff00
/* The mask used to clear the ALT_RSTMGR_COUNTS_NRSTCNT register field value. */
#define ALT_RSTMGR_COUNTS_NRSTCNT_CLR_MSK    0xf00000ff
/* The reset value of the ALT_RSTMGR_COUNTS_NRSTCNT register field. */
#define ALT_RSTMGR_COUNTS_NRSTCNT_RESET      0x800
/* Extracts the ALT_RSTMGR_COUNTS_NRSTCNT field value from a register. */
#define ALT_RSTMGR_COUNTS_NRSTCNT_GET(value) (((value) & 0x0fffff00) >> 8)
/* Produces a ALT_RSTMGR_COUNTS_NRSTCNT register field value suitable for setting the register. */
#define ALT_RSTMGR_COUNTS_NRSTCNT_SET(value) (((value) << 8) & 0x0fffff00)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_RSTMGR_COUNTS.
 */
struct ALT_RSTMGR_COUNTS_s
{
    uint32_t  warmrstcycles :  8;  /* Warm reset release delay count */
    uint32_t  nrstcnt       : 20;  /* nRST Pin Count */
    uint32_t                :  4;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_RSTMGR_COUNTS. */
typedef volatile struct ALT_RSTMGR_COUNTS_s  ALT_RSTMGR_COUNTS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_RSTMGR_COUNTS register from the beginning of the component. */
#define ALT_RSTMGR_COUNTS_OFST        0x8

/*
 * Register : MPU Module Reset Register - mpumodrst
 * 
 * The MPUMODRST register is used by software to trigger module resets (individual
 * module reset signals). Software explicitly asserts and de-asserts module reset
 * signals by writing bits in the appropriate *MODRST register. It is up to
 * software to ensure module reset signals are asserted for the appropriate length
 * of time and are de-asserted in the correct order. It is also up to software to
 * not assert a module reset signal that would prevent software from de-asserting
 * the module reset signal. For example, software should not assert the module
 * reset to the CPU executing the software.
 * 
 * Software writes a bit to 1 to assert the module reset signal and to 0 to de-
 * assert the module reset signal.
 * 
 * All fields except CPU1 are only reset by a cold reset. The CPU1 field is reset
 * by a cold reset. The CPU1 field is also reset by a warm reset if not masked by
 * the corresponding MPUWARMMASK field.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description    
 * :-------|:-------|:------|:----------------
 *  [0]    | RW     | 0x0   | CPU0           
 *  [1]    | RW     | 0x1   | CPU1           
 *  [2]    | RW     | 0x0   | Watchdogs      
 *  [3]    | RW     | 0x0   | SCU/Peripherals
 *  [4]    | RW     | 0x0   | L2             
 *  [31:5] | ???    | 0x0   | *UNDEFINED*    
 * 
 */
/*
 * Field : CPU0 - cpu0
 * 
 * Resets Cortex-A9 CPU0 in MPU. Whe software changes this field from 0 to 1,
 * ittriggers the following sequence:  1. CPU0 reset is asserted. cpu0 clkoff is
 * de-asserted 2. after 32 osc1_clk cycles, cpu0 clkoff is asserted.
 * 
 * When software changes this field from 1 to 0, it triggers the following
 * sequence: 1.CPU0 reset is de-asserted. 2. after 32 cycles, cpu0 clkoff is de-
 * asserted.
 * 
 * Software needs to wait for at least 64 osc1_clk cycles between each change of
 * this field to keep the proper reset/clkoff sequence.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MPUMODRST_CPU0 register field. */
#define ALT_RSTMGR_MPUMODRST_CPU0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MPUMODRST_CPU0 register field. */
#define ALT_RSTMGR_MPUMODRST_CPU0_MSB        0
/* The width in bits of the ALT_RSTMGR_MPUMODRST_CPU0 register field. */
#define ALT_RSTMGR_MPUMODRST_CPU0_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MPUMODRST_CPU0 register field value. */
#define ALT_RSTMGR_MPUMODRST_CPU0_SET_MSK    0x00000001
/* The mask used to clear the ALT_RSTMGR_MPUMODRST_CPU0 register field value. */
#define ALT_RSTMGR_MPUMODRST_CPU0_CLR_MSK    0xfffffffe
/* The reset value of the ALT_RSTMGR_MPUMODRST_CPU0 register field. */
#define ALT_RSTMGR_MPUMODRST_CPU0_RESET      0x0
/* Extracts the ALT_RSTMGR_MPUMODRST_CPU0 field value from a register. */
#define ALT_RSTMGR_MPUMODRST_CPU0_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_RSTMGR_MPUMODRST_CPU0 register field value suitable for setting the register. */
#define ALT_RSTMGR_MPUMODRST_CPU0_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : CPU1 - cpu1
 * 
 * Resets Cortex-A9 CPU1 in MPU.
 * 
 * It is reset to 1 on a cold or warm reset. This holds CPU1 in reset until
 * software is ready to release CPU1 from reset by writing 0 to this field.
 * 
 * On single-core devices, writes to this field are ignored.On dual-core devices,
 * writes to this field trigger the same sequence as writes to the CPU0 field
 * (except the sequence is performed on CPU1).
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MPUMODRST_CPU1 register field. */
#define ALT_RSTMGR_MPUMODRST_CPU1_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MPUMODRST_CPU1 register field. */
#define ALT_RSTMGR_MPUMODRST_CPU1_MSB        1
/* The width in bits of the ALT_RSTMGR_MPUMODRST_CPU1 register field. */
#define ALT_RSTMGR_MPUMODRST_CPU1_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MPUMODRST_CPU1 register field value. */
#define ALT_RSTMGR_MPUMODRST_CPU1_SET_MSK    0x00000002
/* The mask used to clear the ALT_RSTMGR_MPUMODRST_CPU1 register field value. */
#define ALT_RSTMGR_MPUMODRST_CPU1_CLR_MSK    0xfffffffd
/* The reset value of the ALT_RSTMGR_MPUMODRST_CPU1 register field. */
#define ALT_RSTMGR_MPUMODRST_CPU1_RESET      0x1
/* Extracts the ALT_RSTMGR_MPUMODRST_CPU1 field value from a register. */
#define ALT_RSTMGR_MPUMODRST_CPU1_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_RSTMGR_MPUMODRST_CPU1 register field value suitable for setting the register. */
#define ALT_RSTMGR_MPUMODRST_CPU1_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Watchdogs - wds
 * 
 * Resets both per-CPU Watchdog Reset Status registers in MPU.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MPUMODRST_WDS register field. */
#define ALT_RSTMGR_MPUMODRST_WDS_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MPUMODRST_WDS register field. */
#define ALT_RSTMGR_MPUMODRST_WDS_MSB        2
/* The width in bits of the ALT_RSTMGR_MPUMODRST_WDS register field. */
#define ALT_RSTMGR_MPUMODRST_WDS_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MPUMODRST_WDS register field value. */
#define ALT_RSTMGR_MPUMODRST_WDS_SET_MSK    0x00000004
/* The mask used to clear the ALT_RSTMGR_MPUMODRST_WDS register field value. */
#define ALT_RSTMGR_MPUMODRST_WDS_CLR_MSK    0xfffffffb
/* The reset value of the ALT_RSTMGR_MPUMODRST_WDS register field. */
#define ALT_RSTMGR_MPUMODRST_WDS_RESET      0x0
/* Extracts the ALT_RSTMGR_MPUMODRST_WDS field value from a register. */
#define ALT_RSTMGR_MPUMODRST_WDS_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_RSTMGR_MPUMODRST_WDS register field value suitable for setting the register. */
#define ALT_RSTMGR_MPUMODRST_WDS_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : SCU/Peripherals - scuper
 * 
 * Resets SCU and peripherals. Peripherals consist of the interrupt controller,
 * global timer, both per-CPU private timers, and both per-CPU watchdogs (except
 * for the Watchdog Reset Status registers).
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MPUMODRST_SCUPER register field. */
#define ALT_RSTMGR_MPUMODRST_SCUPER_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MPUMODRST_SCUPER register field. */
#define ALT_RSTMGR_MPUMODRST_SCUPER_MSB        3
/* The width in bits of the ALT_RSTMGR_MPUMODRST_SCUPER register field. */
#define ALT_RSTMGR_MPUMODRST_SCUPER_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MPUMODRST_SCUPER register field value. */
#define ALT_RSTMGR_MPUMODRST_SCUPER_SET_MSK    0x00000008
/* The mask used to clear the ALT_RSTMGR_MPUMODRST_SCUPER register field value. */
#define ALT_RSTMGR_MPUMODRST_SCUPER_CLR_MSK    0xfffffff7
/* The reset value of the ALT_RSTMGR_MPUMODRST_SCUPER register field. */
#define ALT_RSTMGR_MPUMODRST_SCUPER_RESET      0x0
/* Extracts the ALT_RSTMGR_MPUMODRST_SCUPER field value from a register. */
#define ALT_RSTMGR_MPUMODRST_SCUPER_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_RSTMGR_MPUMODRST_SCUPER register field value suitable for setting the register. */
#define ALT_RSTMGR_MPUMODRST_SCUPER_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : L2 - l2
 * 
 * Resets L2 cache controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MPUMODRST_L2 register field. */
#define ALT_RSTMGR_MPUMODRST_L2_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MPUMODRST_L2 register field. */
#define ALT_RSTMGR_MPUMODRST_L2_MSB        4
/* The width in bits of the ALT_RSTMGR_MPUMODRST_L2 register field. */
#define ALT_RSTMGR_MPUMODRST_L2_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MPUMODRST_L2 register field value. */
#define ALT_RSTMGR_MPUMODRST_L2_SET_MSK    0x00000010
/* The mask used to clear the ALT_RSTMGR_MPUMODRST_L2 register field value. */
#define ALT_RSTMGR_MPUMODRST_L2_CLR_MSK    0xffffffef
/* The reset value of the ALT_RSTMGR_MPUMODRST_L2 register field. */
#define ALT_RSTMGR_MPUMODRST_L2_RESET      0x0
/* Extracts the ALT_RSTMGR_MPUMODRST_L2 field value from a register. */
#define ALT_RSTMGR_MPUMODRST_L2_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_RSTMGR_MPUMODRST_L2 register field value suitable for setting the register. */
#define ALT_RSTMGR_MPUMODRST_L2_SET(value) (((value) << 4) & 0x00000010)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_RSTMGR_MPUMODRST.
 */
struct ALT_RSTMGR_MPUMODRST_s
{
    uint32_t  cpu0   :  1;  /* CPU0 */
    uint32_t  cpu1   :  1;  /* CPU1 */
    uint32_t  wds    :  1;  /* Watchdogs */
    uint32_t  scuper :  1;  /* SCU/Peripherals */
    uint32_t  l2     :  1;  /* L2 */
    uint32_t         : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_RSTMGR_MPUMODRST. */
typedef volatile struct ALT_RSTMGR_MPUMODRST_s  ALT_RSTMGR_MPUMODRST_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_RSTMGR_MPUMODRST register from the beginning of the component. */
#define ALT_RSTMGR_MPUMODRST_OFST        0x10

/*
 * Register : Peripheral Module Reset Register - permodrst
 * 
 * The PERMODRST register is used by software to trigger module resets (individual
 * module reset signals). Software explicitly asserts and de-asserts module reset
 * signals by writing bits in the appropriate *MODRST register. It is up to
 * software to ensure module reset signals are asserted for the appropriate length
 * of time and are de-asserted in the correct order. It is also up to software to
 * not assert a module reset signal that would prevent software from de-asserting
 * the module reset signal. For example, software should not assert the module
 * reset to the CPU executing the software.
 * 
 * Software writes a bit to 1 to assert the module reset signal and to 0 to de-
 * assert the module reset signal.
 * 
 * All fields are reset by a cold reset.All fields are also reset by a warm reset
 * if not masked by the corresponding PERWARMMASK field.
 * 
 * The reset value of all fields is 1. This holds the corresponding module in reset
 * until software is ready to release the module from reset by writing 0 to its
 * field.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description               
 * :--------|:-------|:------|:---------------------------
 *  [0]     | RW     | 0x1   | EMAC0                     
 *  [1]     | RW     | 0x1   | EMAC1                     
 *  [2]     | RW     | 0x1   | USB0                      
 *  [3]     | RW     | 0x1   | USB1                      
 *  [4]     | RW     | 0x1   | NAND Flash                
 *  [5]     | RW     | 0x1   | QSPI Flash                
 *  [6]     | RW     | 0x1   | L4 Watchdog 0             
 *  [7]     | RW     | 0x1   | L4 Watchdog 1             
 *  [8]     | RW     | 0x1   | OSC1 Timer 0              
 *  [9]     | RW     | 0x1   | OSC1 Timer 1              
 *  [10]    | RW     | 0x1   | SP Timer 0                
 *  [11]    | RW     | 0x1   | SP Timer 1                
 *  [12]    | RW     | 0x1   | I2C0                      
 *  [13]    | RW     | 0x1   | I2C1                      
 *  [14]    | RW     | 0x1   | I2C2                      
 *  [15]    | RW     | 0x1   | I2C3                      
 *  [16]    | RW     | 0x1   | UART0                     
 *  [17]    | RW     | 0x1   | UART1                     
 *  [18]    | RW     | 0x1   | SPIM0                     
 *  [19]    | RW     | 0x1   | SPIM1                     
 *  [20]    | RW     | 0x1   | SPIS0                     
 *  [21]    | RW     | 0x1   | SPIS1                     
 *  [22]    | RW     | 0x1   | SD/MMC                    
 *  [23]    | RW     | 0x1   | CAN0                      
 *  [24]    | RW     | 0x1   | CAN1                      
 *  [25]    | RW     | 0x1   | GPIO0                     
 *  [26]    | RW     | 0x1   | GPIO1                     
 *  [27]    | RW     | 0x1   | GPIO2                     
 *  [28]    | RW     | 0x1   | DMA Controller            
 *  [29]    | RW     | 0x1   | SDRAM Controller Subsystem
 *  [31:30] | ???    | 0x0   | *UNDEFINED*               
 * 
 */
/*
 * Field : EMAC0 - emac0
 * 
 * Resets EMAC0
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_EMAC0 register field. */
#define ALT_RSTMGR_PERMODRST_EMAC0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_EMAC0 register field. */
#define ALT_RSTMGR_PERMODRST_EMAC0_MSB        0
/* The width in bits of the ALT_RSTMGR_PERMODRST_EMAC0 register field. */
#define ALT_RSTMGR_PERMODRST_EMAC0_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_EMAC0 register field value. */
#define ALT_RSTMGR_PERMODRST_EMAC0_SET_MSK    0x00000001
/* The mask used to clear the ALT_RSTMGR_PERMODRST_EMAC0 register field value. */
#define ALT_RSTMGR_PERMODRST_EMAC0_CLR_MSK    0xfffffffe
/* The reset value of the ALT_RSTMGR_PERMODRST_EMAC0 register field. */
#define ALT_RSTMGR_PERMODRST_EMAC0_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_EMAC0 field value from a register. */
#define ALT_RSTMGR_PERMODRST_EMAC0_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_RSTMGR_PERMODRST_EMAC0 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_EMAC0_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : EMAC1 - emac1
 * 
 * Resets EMAC1
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_EMAC1 register field. */
#define ALT_RSTMGR_PERMODRST_EMAC1_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_EMAC1 register field. */
#define ALT_RSTMGR_PERMODRST_EMAC1_MSB        1
/* The width in bits of the ALT_RSTMGR_PERMODRST_EMAC1 register field. */
#define ALT_RSTMGR_PERMODRST_EMAC1_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_EMAC1 register field value. */
#define ALT_RSTMGR_PERMODRST_EMAC1_SET_MSK    0x00000002
/* The mask used to clear the ALT_RSTMGR_PERMODRST_EMAC1 register field value. */
#define ALT_RSTMGR_PERMODRST_EMAC1_CLR_MSK    0xfffffffd
/* The reset value of the ALT_RSTMGR_PERMODRST_EMAC1 register field. */
#define ALT_RSTMGR_PERMODRST_EMAC1_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_EMAC1 field value from a register. */
#define ALT_RSTMGR_PERMODRST_EMAC1_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_RSTMGR_PERMODRST_EMAC1 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_EMAC1_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : USB0 - usb0
 * 
 * Resets USB0
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_USB0 register field. */
#define ALT_RSTMGR_PERMODRST_USB0_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_USB0 register field. */
#define ALT_RSTMGR_PERMODRST_USB0_MSB        2
/* The width in bits of the ALT_RSTMGR_PERMODRST_USB0 register field. */
#define ALT_RSTMGR_PERMODRST_USB0_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_USB0 register field value. */
#define ALT_RSTMGR_PERMODRST_USB0_SET_MSK    0x00000004
/* The mask used to clear the ALT_RSTMGR_PERMODRST_USB0 register field value. */
#define ALT_RSTMGR_PERMODRST_USB0_CLR_MSK    0xfffffffb
/* The reset value of the ALT_RSTMGR_PERMODRST_USB0 register field. */
#define ALT_RSTMGR_PERMODRST_USB0_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_USB0 field value from a register. */
#define ALT_RSTMGR_PERMODRST_USB0_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_RSTMGR_PERMODRST_USB0 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_USB0_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : USB1 - usb1
 * 
 * Resets USB1
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_USB1 register field. */
#define ALT_RSTMGR_PERMODRST_USB1_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_USB1 register field. */
#define ALT_RSTMGR_PERMODRST_USB1_MSB        3
/* The width in bits of the ALT_RSTMGR_PERMODRST_USB1 register field. */
#define ALT_RSTMGR_PERMODRST_USB1_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_USB1 register field value. */
#define ALT_RSTMGR_PERMODRST_USB1_SET_MSK    0x00000008
/* The mask used to clear the ALT_RSTMGR_PERMODRST_USB1 register field value. */
#define ALT_RSTMGR_PERMODRST_USB1_CLR_MSK    0xfffffff7
/* The reset value of the ALT_RSTMGR_PERMODRST_USB1 register field. */
#define ALT_RSTMGR_PERMODRST_USB1_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_USB1 field value from a register. */
#define ALT_RSTMGR_PERMODRST_USB1_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_RSTMGR_PERMODRST_USB1 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_USB1_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : NAND Flash - nand
 * 
 * Resets NAND flash controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_NAND register field. */
#define ALT_RSTMGR_PERMODRST_NAND_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_NAND register field. */
#define ALT_RSTMGR_PERMODRST_NAND_MSB        4
/* The width in bits of the ALT_RSTMGR_PERMODRST_NAND register field. */
#define ALT_RSTMGR_PERMODRST_NAND_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_NAND register field value. */
#define ALT_RSTMGR_PERMODRST_NAND_SET_MSK    0x00000010
/* The mask used to clear the ALT_RSTMGR_PERMODRST_NAND register field value. */
#define ALT_RSTMGR_PERMODRST_NAND_CLR_MSK    0xffffffef
/* The reset value of the ALT_RSTMGR_PERMODRST_NAND register field. */
#define ALT_RSTMGR_PERMODRST_NAND_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_NAND field value from a register. */
#define ALT_RSTMGR_PERMODRST_NAND_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_RSTMGR_PERMODRST_NAND register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_NAND_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : QSPI Flash - qspi
 * 
 * Resets QSPI flash controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_QSPI register field. */
#define ALT_RSTMGR_PERMODRST_QSPI_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_QSPI register field. */
#define ALT_RSTMGR_PERMODRST_QSPI_MSB        5
/* The width in bits of the ALT_RSTMGR_PERMODRST_QSPI register field. */
#define ALT_RSTMGR_PERMODRST_QSPI_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_QSPI register field value. */
#define ALT_RSTMGR_PERMODRST_QSPI_SET_MSK    0x00000020
/* The mask used to clear the ALT_RSTMGR_PERMODRST_QSPI register field value. */
#define ALT_RSTMGR_PERMODRST_QSPI_CLR_MSK    0xffffffdf
/* The reset value of the ALT_RSTMGR_PERMODRST_QSPI register field. */
#define ALT_RSTMGR_PERMODRST_QSPI_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_QSPI field value from a register. */
#define ALT_RSTMGR_PERMODRST_QSPI_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_RSTMGR_PERMODRST_QSPI register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_QSPI_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : L4 Watchdog 0 - l4wd0
 * 
 * Resets watchdog 0 connected to L4
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_L4WD0 register field. */
#define ALT_RSTMGR_PERMODRST_L4WD0_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_L4WD0 register field. */
#define ALT_RSTMGR_PERMODRST_L4WD0_MSB        6
/* The width in bits of the ALT_RSTMGR_PERMODRST_L4WD0 register field. */
#define ALT_RSTMGR_PERMODRST_L4WD0_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_L4WD0 register field value. */
#define ALT_RSTMGR_PERMODRST_L4WD0_SET_MSK    0x00000040
/* The mask used to clear the ALT_RSTMGR_PERMODRST_L4WD0 register field value. */
#define ALT_RSTMGR_PERMODRST_L4WD0_CLR_MSK    0xffffffbf
/* The reset value of the ALT_RSTMGR_PERMODRST_L4WD0 register field. */
#define ALT_RSTMGR_PERMODRST_L4WD0_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_L4WD0 field value from a register. */
#define ALT_RSTMGR_PERMODRST_L4WD0_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_RSTMGR_PERMODRST_L4WD0 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_L4WD0_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : L4 Watchdog 1 - l4wd1
 * 
 * Resets watchdog 1 connected to L4
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_L4WD1 register field. */
#define ALT_RSTMGR_PERMODRST_L4WD1_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_L4WD1 register field. */
#define ALT_RSTMGR_PERMODRST_L4WD1_MSB        7
/* The width in bits of the ALT_RSTMGR_PERMODRST_L4WD1 register field. */
#define ALT_RSTMGR_PERMODRST_L4WD1_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_L4WD1 register field value. */
#define ALT_RSTMGR_PERMODRST_L4WD1_SET_MSK    0x00000080
/* The mask used to clear the ALT_RSTMGR_PERMODRST_L4WD1 register field value. */
#define ALT_RSTMGR_PERMODRST_L4WD1_CLR_MSK    0xffffff7f
/* The reset value of the ALT_RSTMGR_PERMODRST_L4WD1 register field. */
#define ALT_RSTMGR_PERMODRST_L4WD1_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_L4WD1 field value from a register. */
#define ALT_RSTMGR_PERMODRST_L4WD1_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_RSTMGR_PERMODRST_L4WD1 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_L4WD1_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : OSC1 Timer 0 - osc1timer0
 * 
 * Resets OSC1 timer 0 connected to L4
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_OSC1TMR0 register field. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR0_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_OSC1TMR0 register field. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR0_MSB        8
/* The width in bits of the ALT_RSTMGR_PERMODRST_OSC1TMR0 register field. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR0_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_OSC1TMR0 register field value. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR0_SET_MSK    0x00000100
/* The mask used to clear the ALT_RSTMGR_PERMODRST_OSC1TMR0 register field value. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR0_CLR_MSK    0xfffffeff
/* The reset value of the ALT_RSTMGR_PERMODRST_OSC1TMR0 register field. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR0_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_OSC1TMR0 field value from a register. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR0_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_RSTMGR_PERMODRST_OSC1TMR0 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR0_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : OSC1 Timer 1 - osc1timer1
 * 
 * Resets OSC1 timer 1 connected to L4
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_OSC1TMR1 register field. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR1_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_OSC1TMR1 register field. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR1_MSB        9
/* The width in bits of the ALT_RSTMGR_PERMODRST_OSC1TMR1 register field. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR1_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_OSC1TMR1 register field value. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR1_SET_MSK    0x00000200
/* The mask used to clear the ALT_RSTMGR_PERMODRST_OSC1TMR1 register field value. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR1_CLR_MSK    0xfffffdff
/* The reset value of the ALT_RSTMGR_PERMODRST_OSC1TMR1 register field. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR1_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_OSC1TMR1 field value from a register. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR1_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_RSTMGR_PERMODRST_OSC1TMR1 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_OSC1TMR1_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : SP Timer 0 - sptimer0
 * 
 * Resets SP timer 0 connected to L4
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_SPTMR0 register field. */
#define ALT_RSTMGR_PERMODRST_SPTMR0_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_SPTMR0 register field. */
#define ALT_RSTMGR_PERMODRST_SPTMR0_MSB        10
/* The width in bits of the ALT_RSTMGR_PERMODRST_SPTMR0 register field. */
#define ALT_RSTMGR_PERMODRST_SPTMR0_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_SPTMR0 register field value. */
#define ALT_RSTMGR_PERMODRST_SPTMR0_SET_MSK    0x00000400
/* The mask used to clear the ALT_RSTMGR_PERMODRST_SPTMR0 register field value. */
#define ALT_RSTMGR_PERMODRST_SPTMR0_CLR_MSK    0xfffffbff
/* The reset value of the ALT_RSTMGR_PERMODRST_SPTMR0 register field. */
#define ALT_RSTMGR_PERMODRST_SPTMR0_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_SPTMR0 field value from a register. */
#define ALT_RSTMGR_PERMODRST_SPTMR0_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_RSTMGR_PERMODRST_SPTMR0 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_SPTMR0_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : SP Timer 1 - sptimer1
 * 
 * Resets SP timer 1 connected to L4
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_SPTMR1 register field. */
#define ALT_RSTMGR_PERMODRST_SPTMR1_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_SPTMR1 register field. */
#define ALT_RSTMGR_PERMODRST_SPTMR1_MSB        11
/* The width in bits of the ALT_RSTMGR_PERMODRST_SPTMR1 register field. */
#define ALT_RSTMGR_PERMODRST_SPTMR1_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_SPTMR1 register field value. */
#define ALT_RSTMGR_PERMODRST_SPTMR1_SET_MSK    0x00000800
/* The mask used to clear the ALT_RSTMGR_PERMODRST_SPTMR1 register field value. */
#define ALT_RSTMGR_PERMODRST_SPTMR1_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_RSTMGR_PERMODRST_SPTMR1 register field. */
#define ALT_RSTMGR_PERMODRST_SPTMR1_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_SPTMR1 field value from a register. */
#define ALT_RSTMGR_PERMODRST_SPTMR1_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_RSTMGR_PERMODRST_SPTMR1 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_SPTMR1_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : I2C0 - i2c0
 * 
 * Resets I2C0 controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_I2C0 register field. */
#define ALT_RSTMGR_PERMODRST_I2C0_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_I2C0 register field. */
#define ALT_RSTMGR_PERMODRST_I2C0_MSB        12
/* The width in bits of the ALT_RSTMGR_PERMODRST_I2C0 register field. */
#define ALT_RSTMGR_PERMODRST_I2C0_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_I2C0 register field value. */
#define ALT_RSTMGR_PERMODRST_I2C0_SET_MSK    0x00001000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_I2C0 register field value. */
#define ALT_RSTMGR_PERMODRST_I2C0_CLR_MSK    0xffffefff
/* The reset value of the ALT_RSTMGR_PERMODRST_I2C0 register field. */
#define ALT_RSTMGR_PERMODRST_I2C0_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_I2C0 field value from a register. */
#define ALT_RSTMGR_PERMODRST_I2C0_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_RSTMGR_PERMODRST_I2C0 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_I2C0_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : I2C1 - i2c1
 * 
 * Resets I2C1 controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_I2C1 register field. */
#define ALT_RSTMGR_PERMODRST_I2C1_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_I2C1 register field. */
#define ALT_RSTMGR_PERMODRST_I2C1_MSB        13
/* The width in bits of the ALT_RSTMGR_PERMODRST_I2C1 register field. */
#define ALT_RSTMGR_PERMODRST_I2C1_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_I2C1 register field value. */
#define ALT_RSTMGR_PERMODRST_I2C1_SET_MSK    0x00002000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_I2C1 register field value. */
#define ALT_RSTMGR_PERMODRST_I2C1_CLR_MSK    0xffffdfff
/* The reset value of the ALT_RSTMGR_PERMODRST_I2C1 register field. */
#define ALT_RSTMGR_PERMODRST_I2C1_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_I2C1 field value from a register. */
#define ALT_RSTMGR_PERMODRST_I2C1_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_RSTMGR_PERMODRST_I2C1 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_I2C1_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : I2C2 - i2c2
 * 
 * Resets I2C2 controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_I2C2 register field. */
#define ALT_RSTMGR_PERMODRST_I2C2_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_I2C2 register field. */
#define ALT_RSTMGR_PERMODRST_I2C2_MSB        14
/* The width in bits of the ALT_RSTMGR_PERMODRST_I2C2 register field. */
#define ALT_RSTMGR_PERMODRST_I2C2_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_I2C2 register field value. */
#define ALT_RSTMGR_PERMODRST_I2C2_SET_MSK    0x00004000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_I2C2 register field value. */
#define ALT_RSTMGR_PERMODRST_I2C2_CLR_MSK    0xffffbfff
/* The reset value of the ALT_RSTMGR_PERMODRST_I2C2 register field. */
#define ALT_RSTMGR_PERMODRST_I2C2_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_I2C2 field value from a register. */
#define ALT_RSTMGR_PERMODRST_I2C2_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_RSTMGR_PERMODRST_I2C2 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_I2C2_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : I2C3 - i2c3
 * 
 * Resets I2C3 controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_I2C3 register field. */
#define ALT_RSTMGR_PERMODRST_I2C3_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_I2C3 register field. */
#define ALT_RSTMGR_PERMODRST_I2C3_MSB        15
/* The width in bits of the ALT_RSTMGR_PERMODRST_I2C3 register field. */
#define ALT_RSTMGR_PERMODRST_I2C3_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_I2C3 register field value. */
#define ALT_RSTMGR_PERMODRST_I2C3_SET_MSK    0x00008000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_I2C3 register field value. */
#define ALT_RSTMGR_PERMODRST_I2C3_CLR_MSK    0xffff7fff
/* The reset value of the ALT_RSTMGR_PERMODRST_I2C3 register field. */
#define ALT_RSTMGR_PERMODRST_I2C3_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_I2C3 field value from a register. */
#define ALT_RSTMGR_PERMODRST_I2C3_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_RSTMGR_PERMODRST_I2C3 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_I2C3_SET(value) (((value) << 15) & 0x00008000)

/*
 * Field : UART0 - uart0
 * 
 * Resets UART0
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_UART0 register field. */
#define ALT_RSTMGR_PERMODRST_UART0_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_UART0 register field. */
#define ALT_RSTMGR_PERMODRST_UART0_MSB        16
/* The width in bits of the ALT_RSTMGR_PERMODRST_UART0 register field. */
#define ALT_RSTMGR_PERMODRST_UART0_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_UART0 register field value. */
#define ALT_RSTMGR_PERMODRST_UART0_SET_MSK    0x00010000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_UART0 register field value. */
#define ALT_RSTMGR_PERMODRST_UART0_CLR_MSK    0xfffeffff
/* The reset value of the ALT_RSTMGR_PERMODRST_UART0 register field. */
#define ALT_RSTMGR_PERMODRST_UART0_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_UART0 field value from a register. */
#define ALT_RSTMGR_PERMODRST_UART0_GET(value) (((value) & 0x00010000) >> 16)
/* Produces a ALT_RSTMGR_PERMODRST_UART0 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_UART0_SET(value) (((value) << 16) & 0x00010000)

/*
 * Field : UART1 - uart1
 * 
 * Resets UART1
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_UART1 register field. */
#define ALT_RSTMGR_PERMODRST_UART1_LSB        17
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_UART1 register field. */
#define ALT_RSTMGR_PERMODRST_UART1_MSB        17
/* The width in bits of the ALT_RSTMGR_PERMODRST_UART1 register field. */
#define ALT_RSTMGR_PERMODRST_UART1_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_UART1 register field value. */
#define ALT_RSTMGR_PERMODRST_UART1_SET_MSK    0x00020000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_UART1 register field value. */
#define ALT_RSTMGR_PERMODRST_UART1_CLR_MSK    0xfffdffff
/* The reset value of the ALT_RSTMGR_PERMODRST_UART1 register field. */
#define ALT_RSTMGR_PERMODRST_UART1_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_UART1 field value from a register. */
#define ALT_RSTMGR_PERMODRST_UART1_GET(value) (((value) & 0x00020000) >> 17)
/* Produces a ALT_RSTMGR_PERMODRST_UART1 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_UART1_SET(value) (((value) << 17) & 0x00020000)

/*
 * Field : SPIM0 - spim0
 * 
 * Resets SPIM0 controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_SPIM0 register field. */
#define ALT_RSTMGR_PERMODRST_SPIM0_LSB        18
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_SPIM0 register field. */
#define ALT_RSTMGR_PERMODRST_SPIM0_MSB        18
/* The width in bits of the ALT_RSTMGR_PERMODRST_SPIM0 register field. */
#define ALT_RSTMGR_PERMODRST_SPIM0_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_SPIM0 register field value. */
#define ALT_RSTMGR_PERMODRST_SPIM0_SET_MSK    0x00040000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_SPIM0 register field value. */
#define ALT_RSTMGR_PERMODRST_SPIM0_CLR_MSK    0xfffbffff
/* The reset value of the ALT_RSTMGR_PERMODRST_SPIM0 register field. */
#define ALT_RSTMGR_PERMODRST_SPIM0_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_SPIM0 field value from a register. */
#define ALT_RSTMGR_PERMODRST_SPIM0_GET(value) (((value) & 0x00040000) >> 18)
/* Produces a ALT_RSTMGR_PERMODRST_SPIM0 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_SPIM0_SET(value) (((value) << 18) & 0x00040000)

/*
 * Field : SPIM1 - spim1
 * 
 * Resets SPIM1 controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_SPIM1 register field. */
#define ALT_RSTMGR_PERMODRST_SPIM1_LSB        19
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_SPIM1 register field. */
#define ALT_RSTMGR_PERMODRST_SPIM1_MSB        19
/* The width in bits of the ALT_RSTMGR_PERMODRST_SPIM1 register field. */
#define ALT_RSTMGR_PERMODRST_SPIM1_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_SPIM1 register field value. */
#define ALT_RSTMGR_PERMODRST_SPIM1_SET_MSK    0x00080000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_SPIM1 register field value. */
#define ALT_RSTMGR_PERMODRST_SPIM1_CLR_MSK    0xfff7ffff
/* The reset value of the ALT_RSTMGR_PERMODRST_SPIM1 register field. */
#define ALT_RSTMGR_PERMODRST_SPIM1_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_SPIM1 field value from a register. */
#define ALT_RSTMGR_PERMODRST_SPIM1_GET(value) (((value) & 0x00080000) >> 19)
/* Produces a ALT_RSTMGR_PERMODRST_SPIM1 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_SPIM1_SET(value) (((value) << 19) & 0x00080000)

/*
 * Field : SPIS0 - spis0
 * 
 * Resets SPIS0 controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_SPIS0 register field. */
#define ALT_RSTMGR_PERMODRST_SPIS0_LSB        20
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_SPIS0 register field. */
#define ALT_RSTMGR_PERMODRST_SPIS0_MSB        20
/* The width in bits of the ALT_RSTMGR_PERMODRST_SPIS0 register field. */
#define ALT_RSTMGR_PERMODRST_SPIS0_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_SPIS0 register field value. */
#define ALT_RSTMGR_PERMODRST_SPIS0_SET_MSK    0x00100000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_SPIS0 register field value. */
#define ALT_RSTMGR_PERMODRST_SPIS0_CLR_MSK    0xffefffff
/* The reset value of the ALT_RSTMGR_PERMODRST_SPIS0 register field. */
#define ALT_RSTMGR_PERMODRST_SPIS0_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_SPIS0 field value from a register. */
#define ALT_RSTMGR_PERMODRST_SPIS0_GET(value) (((value) & 0x00100000) >> 20)
/* Produces a ALT_RSTMGR_PERMODRST_SPIS0 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_SPIS0_SET(value) (((value) << 20) & 0x00100000)

/*
 * Field : SPIS1 - spis1
 * 
 * Resets SPIS1 controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_SPIS1 register field. */
#define ALT_RSTMGR_PERMODRST_SPIS1_LSB        21
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_SPIS1 register field. */
#define ALT_RSTMGR_PERMODRST_SPIS1_MSB        21
/* The width in bits of the ALT_RSTMGR_PERMODRST_SPIS1 register field. */
#define ALT_RSTMGR_PERMODRST_SPIS1_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_SPIS1 register field value. */
#define ALT_RSTMGR_PERMODRST_SPIS1_SET_MSK    0x00200000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_SPIS1 register field value. */
#define ALT_RSTMGR_PERMODRST_SPIS1_CLR_MSK    0xffdfffff
/* The reset value of the ALT_RSTMGR_PERMODRST_SPIS1 register field. */
#define ALT_RSTMGR_PERMODRST_SPIS1_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_SPIS1 field value from a register. */
#define ALT_RSTMGR_PERMODRST_SPIS1_GET(value) (((value) & 0x00200000) >> 21)
/* Produces a ALT_RSTMGR_PERMODRST_SPIS1 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_SPIS1_SET(value) (((value) << 21) & 0x00200000)

/*
 * Field : SD/MMC - sdmmc
 * 
 * Resets SD/MMC controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_SDMMC register field. */
#define ALT_RSTMGR_PERMODRST_SDMMC_LSB        22
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_SDMMC register field. */
#define ALT_RSTMGR_PERMODRST_SDMMC_MSB        22
/* The width in bits of the ALT_RSTMGR_PERMODRST_SDMMC register field. */
#define ALT_RSTMGR_PERMODRST_SDMMC_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_SDMMC register field value. */
#define ALT_RSTMGR_PERMODRST_SDMMC_SET_MSK    0x00400000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_SDMMC register field value. */
#define ALT_RSTMGR_PERMODRST_SDMMC_CLR_MSK    0xffbfffff
/* The reset value of the ALT_RSTMGR_PERMODRST_SDMMC register field. */
#define ALT_RSTMGR_PERMODRST_SDMMC_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_SDMMC field value from a register. */
#define ALT_RSTMGR_PERMODRST_SDMMC_GET(value) (((value) & 0x00400000) >> 22)
/* Produces a ALT_RSTMGR_PERMODRST_SDMMC register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_SDMMC_SET(value) (((value) << 22) & 0x00400000)

/*
 * Field : CAN0 - can0
 * 
 * Resets CAN0 controller.
 * 
 * Writes to this field on devices not containing CAN controllers will be ignored.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_CAN0 register field. */
#define ALT_RSTMGR_PERMODRST_CAN0_LSB        23
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_CAN0 register field. */
#define ALT_RSTMGR_PERMODRST_CAN0_MSB        23
/* The width in bits of the ALT_RSTMGR_PERMODRST_CAN0 register field. */
#define ALT_RSTMGR_PERMODRST_CAN0_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_CAN0 register field value. */
#define ALT_RSTMGR_PERMODRST_CAN0_SET_MSK    0x00800000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_CAN0 register field value. */
#define ALT_RSTMGR_PERMODRST_CAN0_CLR_MSK    0xff7fffff
/* The reset value of the ALT_RSTMGR_PERMODRST_CAN0 register field. */
#define ALT_RSTMGR_PERMODRST_CAN0_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_CAN0 field value from a register. */
#define ALT_RSTMGR_PERMODRST_CAN0_GET(value) (((value) & 0x00800000) >> 23)
/* Produces a ALT_RSTMGR_PERMODRST_CAN0 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_CAN0_SET(value) (((value) << 23) & 0x00800000)

/*
 * Field : CAN1 - can1
 * 
 * Resets CAN1 controller.
 * 
 * Writes to this field on devices not containing CAN controllers will be ignored.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_CAN1 register field. */
#define ALT_RSTMGR_PERMODRST_CAN1_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_CAN1 register field. */
#define ALT_RSTMGR_PERMODRST_CAN1_MSB        24
/* The width in bits of the ALT_RSTMGR_PERMODRST_CAN1 register field. */
#define ALT_RSTMGR_PERMODRST_CAN1_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_CAN1 register field value. */
#define ALT_RSTMGR_PERMODRST_CAN1_SET_MSK    0x01000000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_CAN1 register field value. */
#define ALT_RSTMGR_PERMODRST_CAN1_CLR_MSK    0xfeffffff
/* The reset value of the ALT_RSTMGR_PERMODRST_CAN1 register field. */
#define ALT_RSTMGR_PERMODRST_CAN1_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_CAN1 field value from a register. */
#define ALT_RSTMGR_PERMODRST_CAN1_GET(value) (((value) & 0x01000000) >> 24)
/* Produces a ALT_RSTMGR_PERMODRST_CAN1 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_CAN1_SET(value) (((value) << 24) & 0x01000000)

/*
 * Field : GPIO0 - gpio0
 * 
 * Resets GPIO0
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_GPIO0 register field. */
#define ALT_RSTMGR_PERMODRST_GPIO0_LSB        25
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_GPIO0 register field. */
#define ALT_RSTMGR_PERMODRST_GPIO0_MSB        25
/* The width in bits of the ALT_RSTMGR_PERMODRST_GPIO0 register field. */
#define ALT_RSTMGR_PERMODRST_GPIO0_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_GPIO0 register field value. */
#define ALT_RSTMGR_PERMODRST_GPIO0_SET_MSK    0x02000000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_GPIO0 register field value. */
#define ALT_RSTMGR_PERMODRST_GPIO0_CLR_MSK    0xfdffffff
/* The reset value of the ALT_RSTMGR_PERMODRST_GPIO0 register field. */
#define ALT_RSTMGR_PERMODRST_GPIO0_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_GPIO0 field value from a register. */
#define ALT_RSTMGR_PERMODRST_GPIO0_GET(value) (((value) & 0x02000000) >> 25)
/* Produces a ALT_RSTMGR_PERMODRST_GPIO0 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_GPIO0_SET(value) (((value) << 25) & 0x02000000)

/*
 * Field : GPIO1 - gpio1
 * 
 * Resets GPIO1
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_GPIO1 register field. */
#define ALT_RSTMGR_PERMODRST_GPIO1_LSB        26
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_GPIO1 register field. */
#define ALT_RSTMGR_PERMODRST_GPIO1_MSB        26
/* The width in bits of the ALT_RSTMGR_PERMODRST_GPIO1 register field. */
#define ALT_RSTMGR_PERMODRST_GPIO1_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_GPIO1 register field value. */
#define ALT_RSTMGR_PERMODRST_GPIO1_SET_MSK    0x04000000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_GPIO1 register field value. */
#define ALT_RSTMGR_PERMODRST_GPIO1_CLR_MSK    0xfbffffff
/* The reset value of the ALT_RSTMGR_PERMODRST_GPIO1 register field. */
#define ALT_RSTMGR_PERMODRST_GPIO1_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_GPIO1 field value from a register. */
#define ALT_RSTMGR_PERMODRST_GPIO1_GET(value) (((value) & 0x04000000) >> 26)
/* Produces a ALT_RSTMGR_PERMODRST_GPIO1 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_GPIO1_SET(value) (((value) << 26) & 0x04000000)

/*
 * Field : GPIO2 - gpio2
 * 
 * Resets GPIO2
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_GPIO2 register field. */
#define ALT_RSTMGR_PERMODRST_GPIO2_LSB        27
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_GPIO2 register field. */
#define ALT_RSTMGR_PERMODRST_GPIO2_MSB        27
/* The width in bits of the ALT_RSTMGR_PERMODRST_GPIO2 register field. */
#define ALT_RSTMGR_PERMODRST_GPIO2_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_GPIO2 register field value. */
#define ALT_RSTMGR_PERMODRST_GPIO2_SET_MSK    0x08000000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_GPIO2 register field value. */
#define ALT_RSTMGR_PERMODRST_GPIO2_CLR_MSK    0xf7ffffff
/* The reset value of the ALT_RSTMGR_PERMODRST_GPIO2 register field. */
#define ALT_RSTMGR_PERMODRST_GPIO2_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_GPIO2 field value from a register. */
#define ALT_RSTMGR_PERMODRST_GPIO2_GET(value) (((value) & 0x08000000) >> 27)
/* Produces a ALT_RSTMGR_PERMODRST_GPIO2 register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_GPIO2_SET(value) (((value) << 27) & 0x08000000)

/*
 * Field : DMA Controller - dma
 * 
 * Resets DMA controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_DMA register field. */
#define ALT_RSTMGR_PERMODRST_DMA_LSB        28
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_DMA register field. */
#define ALT_RSTMGR_PERMODRST_DMA_MSB        28
/* The width in bits of the ALT_RSTMGR_PERMODRST_DMA register field. */
#define ALT_RSTMGR_PERMODRST_DMA_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_DMA register field value. */
#define ALT_RSTMGR_PERMODRST_DMA_SET_MSK    0x10000000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_DMA register field value. */
#define ALT_RSTMGR_PERMODRST_DMA_CLR_MSK    0xefffffff
/* The reset value of the ALT_RSTMGR_PERMODRST_DMA register field. */
#define ALT_RSTMGR_PERMODRST_DMA_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_DMA field value from a register. */
#define ALT_RSTMGR_PERMODRST_DMA_GET(value) (((value) & 0x10000000) >> 28)
/* Produces a ALT_RSTMGR_PERMODRST_DMA register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_DMA_SET(value) (((value) << 28) & 0x10000000)

/*
 * Field : SDRAM Controller Subsystem - sdr
 * 
 * Resets SDRAM Controller Subsystem affected by a warm or cold reset.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PERMODRST_SDR register field. */
#define ALT_RSTMGR_PERMODRST_SDR_LSB        29
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PERMODRST_SDR register field. */
#define ALT_RSTMGR_PERMODRST_SDR_MSB        29
/* The width in bits of the ALT_RSTMGR_PERMODRST_SDR register field. */
#define ALT_RSTMGR_PERMODRST_SDR_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PERMODRST_SDR register field value. */
#define ALT_RSTMGR_PERMODRST_SDR_SET_MSK    0x20000000
/* The mask used to clear the ALT_RSTMGR_PERMODRST_SDR register field value. */
#define ALT_RSTMGR_PERMODRST_SDR_CLR_MSK    0xdfffffff
/* The reset value of the ALT_RSTMGR_PERMODRST_SDR register field. */
#define ALT_RSTMGR_PERMODRST_SDR_RESET      0x1
/* Extracts the ALT_RSTMGR_PERMODRST_SDR field value from a register. */
#define ALT_RSTMGR_PERMODRST_SDR_GET(value) (((value) & 0x20000000) >> 29)
/* Produces a ALT_RSTMGR_PERMODRST_SDR register field value suitable for setting the register. */
#define ALT_RSTMGR_PERMODRST_SDR_SET(value) (((value) << 29) & 0x20000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_RSTMGR_PERMODRST.
 */
struct ALT_RSTMGR_PERMODRST_s
{
    uint32_t  emac0      :  1;  /* EMAC0 */
    uint32_t  emac1      :  1;  /* EMAC1 */
    uint32_t  usb0       :  1;  /* USB0 */
    uint32_t  usb1       :  1;  /* USB1 */
    uint32_t  nand       :  1;  /* NAND Flash */
    uint32_t  qspi       :  1;  /* QSPI Flash */
    uint32_t  l4wd0      :  1;  /* L4 Watchdog 0 */
    uint32_t  l4wd1      :  1;  /* L4 Watchdog 1 */
    uint32_t  osc1timer0 :  1;  /* OSC1 Timer 0 */
    uint32_t  osc1timer1 :  1;  /* OSC1 Timer 1 */
    uint32_t  sptimer0   :  1;  /* SP Timer 0 */
    uint32_t  sptimer1   :  1;  /* SP Timer 1 */
    uint32_t  i2c0       :  1;  /* I2C0 */
    uint32_t  i2c1       :  1;  /* I2C1 */
    uint32_t  i2c2       :  1;  /* I2C2 */
    uint32_t  i2c3       :  1;  /* I2C3 */
    uint32_t  uart0      :  1;  /* UART0 */
    uint32_t  uart1      :  1;  /* UART1 */
    uint32_t  spim0      :  1;  /* SPIM0 */
    uint32_t  spim1      :  1;  /* SPIM1 */
    uint32_t  spis0      :  1;  /* SPIS0 */
    uint32_t  spis1      :  1;  /* SPIS1 */
    uint32_t  sdmmc      :  1;  /* SD/MMC */
    uint32_t  can0       :  1;  /* CAN0 */
    uint32_t  can1       :  1;  /* CAN1 */
    uint32_t  gpio0      :  1;  /* GPIO0 */
    uint32_t  gpio1      :  1;  /* GPIO1 */
    uint32_t  gpio2      :  1;  /* GPIO2 */
    uint32_t  dma        :  1;  /* DMA Controller */
    uint32_t  sdr        :  1;  /* SDRAM Controller Subsystem */
    uint32_t             :  2;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_RSTMGR_PERMODRST. */
typedef volatile struct ALT_RSTMGR_PERMODRST_s  ALT_RSTMGR_PERMODRST_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_RSTMGR_PERMODRST register from the beginning of the component. */
#define ALT_RSTMGR_PERMODRST_OFST        0x14

/*
 * Register : Peripheral 2 Module Reset Register - per2modrst
 * 
 * The PER2MODRST register is used by software to trigger module resets (individual
 * module reset signals). Software explicitly asserts and de-asserts module reset
 * signals by writing bits in the appropriate *MODRST register. It is up to
 * software to ensure module reset signals are asserted for the appropriate length
 * of time and are de-asserted in the correct order. It is also up to software to
 * not assert a module reset signal that would prevent software from de-asserting
 * the module reset signal. For example, software should not assert the module
 * reset to the CPU executing the software.
 * 
 * Software writes a bit to 1 to assert the module reset signal and to 0 to de-
 * assert the module reset signal.
 * 
 * All fields are reset by a cold reset.All fields are also reset by a warm reset
 * if not masked by the corresponding PERWARMMASK field.
 * 
 * The reset value of all fields is 1. This holds the corresponding module in reset
 * until software is ready to release the module from reset by writing 0 to its
 * field.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [0]    | RW     | 0x1   | FPGA DMA0  
 *  [1]    | RW     | 0x1   | FPGA DMA1  
 *  [2]    | RW     | 0x1   | FPGA DMA2  
 *  [3]    | RW     | 0x1   | FPGA DMA3  
 *  [4]    | RW     | 0x1   | FPGA DMA4  
 *  [5]    | RW     | 0x1   | FPGA DMA5  
 *  [6]    | RW     | 0x1   | FPGA DMA6  
 *  [7]    | RW     | 0x1   | FPGA DMA7  
 *  [31:8] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : FPGA DMA0 - dmaif0
 * 
 * Resets DMA channel 0 interface adapter between FPGA Fabric and HPS DMA
 * Controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF0 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF0 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF0_MSB        0
/* The width in bits of the ALT_RSTMGR_PER2MODRST_DMAIF0 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF0_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PER2MODRST_DMAIF0 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF0_SET_MSK    0x00000001
/* The mask used to clear the ALT_RSTMGR_PER2MODRST_DMAIF0 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF0_CLR_MSK    0xfffffffe
/* The reset value of the ALT_RSTMGR_PER2MODRST_DMAIF0 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF0_RESET      0x1
/* Extracts the ALT_RSTMGR_PER2MODRST_DMAIF0 field value from a register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF0_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_RSTMGR_PER2MODRST_DMAIF0 register field value suitable for setting the register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF0_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : FPGA DMA1 - dmaif1
 * 
 * Resets DMA channel 1 interface adapter between FPGA Fabric and HPS DMA
 * Controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF1 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF1_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF1 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF1_MSB        1
/* The width in bits of the ALT_RSTMGR_PER2MODRST_DMAIF1 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF1_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PER2MODRST_DMAIF1 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF1_SET_MSK    0x00000002
/* The mask used to clear the ALT_RSTMGR_PER2MODRST_DMAIF1 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF1_CLR_MSK    0xfffffffd
/* The reset value of the ALT_RSTMGR_PER2MODRST_DMAIF1 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF1_RESET      0x1
/* Extracts the ALT_RSTMGR_PER2MODRST_DMAIF1 field value from a register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF1_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_RSTMGR_PER2MODRST_DMAIF1 register field value suitable for setting the register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF1_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : FPGA DMA2 - dmaif2
 * 
 * Resets DMA channel 2 interface adapter between FPGA Fabric and HPS DMA
 * Controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF2 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF2_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF2 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF2_MSB        2
/* The width in bits of the ALT_RSTMGR_PER2MODRST_DMAIF2 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF2_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PER2MODRST_DMAIF2 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF2_SET_MSK    0x00000004
/* The mask used to clear the ALT_RSTMGR_PER2MODRST_DMAIF2 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF2_CLR_MSK    0xfffffffb
/* The reset value of the ALT_RSTMGR_PER2MODRST_DMAIF2 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF2_RESET      0x1
/* Extracts the ALT_RSTMGR_PER2MODRST_DMAIF2 field value from a register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF2_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_RSTMGR_PER2MODRST_DMAIF2 register field value suitable for setting the register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF2_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : FPGA DMA3 - dmaif3
 * 
 * Resets DMA channel 3 interface adapter between FPGA Fabric and HPS DMA
 * Controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF3 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF3_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF3 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF3_MSB        3
/* The width in bits of the ALT_RSTMGR_PER2MODRST_DMAIF3 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF3_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PER2MODRST_DMAIF3 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF3_SET_MSK    0x00000008
/* The mask used to clear the ALT_RSTMGR_PER2MODRST_DMAIF3 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF3_CLR_MSK    0xfffffff7
/* The reset value of the ALT_RSTMGR_PER2MODRST_DMAIF3 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF3_RESET      0x1
/* Extracts the ALT_RSTMGR_PER2MODRST_DMAIF3 field value from a register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF3_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_RSTMGR_PER2MODRST_DMAIF3 register field value suitable for setting the register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF3_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : FPGA DMA4 - dmaif4
 * 
 * Resets DMA channel 4 interface adapter between FPGA Fabric and HPS DMA
 * Controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF4 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF4_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF4 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF4_MSB        4
/* The width in bits of the ALT_RSTMGR_PER2MODRST_DMAIF4 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF4_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PER2MODRST_DMAIF4 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF4_SET_MSK    0x00000010
/* The mask used to clear the ALT_RSTMGR_PER2MODRST_DMAIF4 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF4_CLR_MSK    0xffffffef
/* The reset value of the ALT_RSTMGR_PER2MODRST_DMAIF4 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF4_RESET      0x1
/* Extracts the ALT_RSTMGR_PER2MODRST_DMAIF4 field value from a register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF4_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_RSTMGR_PER2MODRST_DMAIF4 register field value suitable for setting the register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF4_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : FPGA DMA5 - dmaif5
 * 
 * Resets DMA channel 5 interface adapter between FPGA Fabric and HPS DMA
 * Controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF5 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF5_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF5 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF5_MSB        5
/* The width in bits of the ALT_RSTMGR_PER2MODRST_DMAIF5 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF5_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PER2MODRST_DMAIF5 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF5_SET_MSK    0x00000020
/* The mask used to clear the ALT_RSTMGR_PER2MODRST_DMAIF5 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF5_CLR_MSK    0xffffffdf
/* The reset value of the ALT_RSTMGR_PER2MODRST_DMAIF5 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF5_RESET      0x1
/* Extracts the ALT_RSTMGR_PER2MODRST_DMAIF5 field value from a register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF5_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_RSTMGR_PER2MODRST_DMAIF5 register field value suitable for setting the register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF5_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : FPGA DMA6 - dmaif6
 * 
 * Resets DMA channel 6 interface adapter between FPGA Fabric and HPS DMA
 * Controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF6 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF6_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF6 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF6_MSB        6
/* The width in bits of the ALT_RSTMGR_PER2MODRST_DMAIF6 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF6_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PER2MODRST_DMAIF6 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF6_SET_MSK    0x00000040
/* The mask used to clear the ALT_RSTMGR_PER2MODRST_DMAIF6 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF6_CLR_MSK    0xffffffbf
/* The reset value of the ALT_RSTMGR_PER2MODRST_DMAIF6 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF6_RESET      0x1
/* Extracts the ALT_RSTMGR_PER2MODRST_DMAIF6 field value from a register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF6_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_RSTMGR_PER2MODRST_DMAIF6 register field value suitable for setting the register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF6_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : FPGA DMA7 - dmaif7
 * 
 * Resets DMA channel 7 interface adapter between FPGA Fabric and HPS DMA
 * Controller
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF7 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF7_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_PER2MODRST_DMAIF7 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF7_MSB        7
/* The width in bits of the ALT_RSTMGR_PER2MODRST_DMAIF7 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF7_WIDTH      1
/* The mask used to set the ALT_RSTMGR_PER2MODRST_DMAIF7 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF7_SET_MSK    0x00000080
/* The mask used to clear the ALT_RSTMGR_PER2MODRST_DMAIF7 register field value. */
#define ALT_RSTMGR_PER2MODRST_DMAIF7_CLR_MSK    0xffffff7f
/* The reset value of the ALT_RSTMGR_PER2MODRST_DMAIF7 register field. */
#define ALT_RSTMGR_PER2MODRST_DMAIF7_RESET      0x1
/* Extracts the ALT_RSTMGR_PER2MODRST_DMAIF7 field value from a register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF7_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_RSTMGR_PER2MODRST_DMAIF7 register field value suitable for setting the register. */
#define ALT_RSTMGR_PER2MODRST_DMAIF7_SET(value) (((value) << 7) & 0x00000080)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_RSTMGR_PER2MODRST.
 */
struct ALT_RSTMGR_PER2MODRST_s
{
    uint32_t  dmaif0 :  1;  /* FPGA DMA0 */
    uint32_t  dmaif1 :  1;  /* FPGA DMA1 */
    uint32_t  dmaif2 :  1;  /* FPGA DMA2 */
    uint32_t  dmaif3 :  1;  /* FPGA DMA3 */
    uint32_t  dmaif4 :  1;  /* FPGA DMA4 */
    uint32_t  dmaif5 :  1;  /* FPGA DMA5 */
    uint32_t  dmaif6 :  1;  /* FPGA DMA6 */
    uint32_t  dmaif7 :  1;  /* FPGA DMA7 */
    uint32_t         : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_RSTMGR_PER2MODRST. */
typedef volatile struct ALT_RSTMGR_PER2MODRST_s  ALT_RSTMGR_PER2MODRST_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_RSTMGR_PER2MODRST register from the beginning of the component. */
#define ALT_RSTMGR_PER2MODRST_OFST        0x18

/*
 * Register : Bridge Module Reset Register - brgmodrst
 * 
 * The BRGMODRST register is used by software to trigger module resets (individual
 * module reset signals). Software explicitly asserts and de-asserts module reset
 * signals by writing bits in the appropriate *MODRST register. It is up to
 * software to ensure module reset signals are asserted for the appropriate length
 * of time and are de-asserted in the correct order. It is also up to software to
 * not assert a module reset signal that would prevent software from de-asserting
 * the module reset signal. For example, software should not assert the module
 * reset to the CPU executing the software.
 * 
 * Software writes a bit to 1 to assert the module reset signal and to 0 to de-
 * assert the module reset signal.
 * 
 * All fields are reset by a cold reset.All fields are also reset by a warm reset
 * if not masked by the corresponding BRGWARMMASK field.
 * 
 * The reset value of all fields is 1. This holds the corresponding module in reset
 * until software is ready to release the module from reset by writing 0 to its
 * field.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description      
 * :-------|:-------|:------|:------------------
 *  [0]    | RW     | 0x1   | HPS2FPGA Bridge  
 *  [1]    | RW     | 0x1   | LWHPS2FPGA Bridge
 *  [2]    | RW     | 0x1   | FPGA2HPS Bridge  
 *  [31:3] | ???    | 0x0   | *UNDEFINED*      
 * 
 */
/*
 * Field : HPS2FPGA Bridge - hps2fpga
 * 
 * Resets HPS2FPGA Bridge
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_BRGMODRST_H2F register field. */
#define ALT_RSTMGR_BRGMODRST_H2F_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_BRGMODRST_H2F register field. */
#define ALT_RSTMGR_BRGMODRST_H2F_MSB        0
/* The width in bits of the ALT_RSTMGR_BRGMODRST_H2F register field. */
#define ALT_RSTMGR_BRGMODRST_H2F_WIDTH      1
/* The mask used to set the ALT_RSTMGR_BRGMODRST_H2F register field value. */
#define ALT_RSTMGR_BRGMODRST_H2F_SET_MSK    0x00000001
/* The mask used to clear the ALT_RSTMGR_BRGMODRST_H2F register field value. */
#define ALT_RSTMGR_BRGMODRST_H2F_CLR_MSK    0xfffffffe
/* The reset value of the ALT_RSTMGR_BRGMODRST_H2F register field. */
#define ALT_RSTMGR_BRGMODRST_H2F_RESET      0x1
/* Extracts the ALT_RSTMGR_BRGMODRST_H2F field value from a register. */
#define ALT_RSTMGR_BRGMODRST_H2F_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_RSTMGR_BRGMODRST_H2F register field value suitable for setting the register. */
#define ALT_RSTMGR_BRGMODRST_H2F_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : LWHPS2FPGA Bridge - lwhps2fpga
 * 
 * Resets LWHPS2FPGA Bridge
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_BRGMODRST_LWH2F register field. */
#define ALT_RSTMGR_BRGMODRST_LWH2F_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_BRGMODRST_LWH2F register field. */
#define ALT_RSTMGR_BRGMODRST_LWH2F_MSB        1
/* The width in bits of the ALT_RSTMGR_BRGMODRST_LWH2F register field. */
#define ALT_RSTMGR_BRGMODRST_LWH2F_WIDTH      1
/* The mask used to set the ALT_RSTMGR_BRGMODRST_LWH2F register field value. */
#define ALT_RSTMGR_BRGMODRST_LWH2F_SET_MSK    0x00000002
/* The mask used to clear the ALT_RSTMGR_BRGMODRST_LWH2F register field value. */
#define ALT_RSTMGR_BRGMODRST_LWH2F_CLR_MSK    0xfffffffd
/* The reset value of the ALT_RSTMGR_BRGMODRST_LWH2F register field. */
#define ALT_RSTMGR_BRGMODRST_LWH2F_RESET      0x1
/* Extracts the ALT_RSTMGR_BRGMODRST_LWH2F field value from a register. */
#define ALT_RSTMGR_BRGMODRST_LWH2F_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_RSTMGR_BRGMODRST_LWH2F register field value suitable for setting the register. */
#define ALT_RSTMGR_BRGMODRST_LWH2F_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : FPGA2HPS Bridge - fpga2hps
 * 
 * Resets FPGA2HPS Bridge
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_BRGMODRST_F2H register field. */
#define ALT_RSTMGR_BRGMODRST_F2H_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_BRGMODRST_F2H register field. */
#define ALT_RSTMGR_BRGMODRST_F2H_MSB        2
/* The width in bits of the ALT_RSTMGR_BRGMODRST_F2H register field. */
#define ALT_RSTMGR_BRGMODRST_F2H_WIDTH      1
/* The mask used to set the ALT_RSTMGR_BRGMODRST_F2H register field value. */
#define ALT_RSTMGR_BRGMODRST_F2H_SET_MSK    0x00000004
/* The mask used to clear the ALT_RSTMGR_BRGMODRST_F2H register field value. */
#define ALT_RSTMGR_BRGMODRST_F2H_CLR_MSK    0xfffffffb
/* The reset value of the ALT_RSTMGR_BRGMODRST_F2H register field. */
#define ALT_RSTMGR_BRGMODRST_F2H_RESET      0x1
/* Extracts the ALT_RSTMGR_BRGMODRST_F2H field value from a register. */
#define ALT_RSTMGR_BRGMODRST_F2H_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_RSTMGR_BRGMODRST_F2H register field value suitable for setting the register. */
#define ALT_RSTMGR_BRGMODRST_F2H_SET(value) (((value) << 2) & 0x00000004)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_RSTMGR_BRGMODRST.
 */
struct ALT_RSTMGR_BRGMODRST_s
{
    uint32_t  hps2fpga   :  1;  /* HPS2FPGA Bridge */
    uint32_t  lwhps2fpga :  1;  /* LWHPS2FPGA Bridge */
    uint32_t  fpga2hps   :  1;  /* FPGA2HPS Bridge */
    uint32_t             : 29;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_RSTMGR_BRGMODRST. */
typedef volatile struct ALT_RSTMGR_BRGMODRST_s  ALT_RSTMGR_BRGMODRST_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_RSTMGR_BRGMODRST register from the beginning of the component. */
#define ALT_RSTMGR_BRGMODRST_OFST        0x1c

/*
 * Register : Miscellaneous Module Reset Register - miscmodrst
 * 
 * The MISCMODRST register is used by software to trigger module resets (individual
 * module reset signals). Software explicitly asserts and de-asserts module reset
 * signals by writing bits in the appropriate *MODRST register. It is up to
 * software to ensure module reset signals are asserted for the appropriate length
 * of time and are de-asserted in the correct order. It is also up to software to
 * not assert a module reset signal that would prevent software from de-asserting
 * the module reset signal. For example, software should not assert the module
 * reset to the CPU executing the software.
 * 
 * Software writes a bit to 1 to assert the module reset signal and to 0 to de-
 * assert the module reset signal.
 * 
 * All fields are only reset by a cold reset
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                          
 * :--------|:-------|:------|:--------------------------------------
 *  [0]     | RW     | 0x0   | Boot ROM                             
 *  [1]     | RW     | 0x0   | On-chip RAM                          
 *  [2]     | RW     | 0x0   | System Manager (Cold or Warm)        
 *  [3]     | RW     | 0x0   | System Manager (Cold-only)           
 *  [4]     | RW     | 0x0   | FPGA Manager                         
 *  [5]     | RW     | 0x0   | ACP ID Mapper                        
 *  [6]     | RW     | 0x0   | HPS to FPGA Core (Cold or Warm)      
 *  [7]     | RW     | 0x0   | HPS to FPGA Core (Cold-only)         
 *  [8]     | RW     | 0x0   | nRST Pin                             
 *  [9]     | RW     | 0x0   | Timestamp                            
 *  [10]    | RW     | 0x0   | Clock Manager                        
 *  [11]    | RW     | 0x0   | Scan Manager                         
 *  [12]    | RW     | 0x0   | Freeze Controller                    
 *  [13]    | RW     | 0x0   | System/Debug                         
 *  [14]    | RW     | 0x0   | Debug                                
 *  [15]    | RW     | 0x0   | TAP Controller                       
 *  [16]    | RW     | 0x0   | SDRAM Controller Subsystem Cold Reset
 *  [31:17] | ???    | 0x0   | *UNDEFINED*                          
 * 
 */
/*
 * Field : Boot ROM - rom
 * 
 * Resets Boot ROM
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_ROM register field. */
#define ALT_RSTMGR_MISCMODRST_ROM_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_ROM register field. */
#define ALT_RSTMGR_MISCMODRST_ROM_MSB        0
/* The width in bits of the ALT_RSTMGR_MISCMODRST_ROM register field. */
#define ALT_RSTMGR_MISCMODRST_ROM_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_ROM register field value. */
#define ALT_RSTMGR_MISCMODRST_ROM_SET_MSK    0x00000001
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_ROM register field value. */
#define ALT_RSTMGR_MISCMODRST_ROM_CLR_MSK    0xfffffffe
/* The reset value of the ALT_RSTMGR_MISCMODRST_ROM register field. */
#define ALT_RSTMGR_MISCMODRST_ROM_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_ROM field value from a register. */
#define ALT_RSTMGR_MISCMODRST_ROM_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_RSTMGR_MISCMODRST_ROM register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_ROM_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : On-chip RAM - ocram
 * 
 * Resets On-chip RAM
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_OCRAM register field. */
#define ALT_RSTMGR_MISCMODRST_OCRAM_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_OCRAM register field. */
#define ALT_RSTMGR_MISCMODRST_OCRAM_MSB        1
/* The width in bits of the ALT_RSTMGR_MISCMODRST_OCRAM register field. */
#define ALT_RSTMGR_MISCMODRST_OCRAM_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_OCRAM register field value. */
#define ALT_RSTMGR_MISCMODRST_OCRAM_SET_MSK    0x00000002
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_OCRAM register field value. */
#define ALT_RSTMGR_MISCMODRST_OCRAM_CLR_MSK    0xfffffffd
/* The reset value of the ALT_RSTMGR_MISCMODRST_OCRAM register field. */
#define ALT_RSTMGR_MISCMODRST_OCRAM_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_OCRAM field value from a register. */
#define ALT_RSTMGR_MISCMODRST_OCRAM_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_RSTMGR_MISCMODRST_OCRAM register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_OCRAM_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : System Manager (Cold or Warm) - sysmgr
 * 
 * Resets logic in System Manager that doesn't differentiate between cold and warm
 * resets
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_SYSMGR register field. */
#define ALT_RSTMGR_MISCMODRST_SYSMGR_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_SYSMGR register field. */
#define ALT_RSTMGR_MISCMODRST_SYSMGR_MSB        2
/* The width in bits of the ALT_RSTMGR_MISCMODRST_SYSMGR register field. */
#define ALT_RSTMGR_MISCMODRST_SYSMGR_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_SYSMGR register field value. */
#define ALT_RSTMGR_MISCMODRST_SYSMGR_SET_MSK    0x00000004
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_SYSMGR register field value. */
#define ALT_RSTMGR_MISCMODRST_SYSMGR_CLR_MSK    0xfffffffb
/* The reset value of the ALT_RSTMGR_MISCMODRST_SYSMGR register field. */
#define ALT_RSTMGR_MISCMODRST_SYSMGR_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_SYSMGR field value from a register. */
#define ALT_RSTMGR_MISCMODRST_SYSMGR_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_RSTMGR_MISCMODRST_SYSMGR register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_SYSMGR_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : System Manager (Cold-only) - sysmgrcold
 * 
 * Resets logic in System Manager that is only reset by a cold reset (ignores warm
 * reset)
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_SYSMGRCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_SYSMGRCOLD_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_SYSMGRCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_SYSMGRCOLD_MSB        3
/* The width in bits of the ALT_RSTMGR_MISCMODRST_SYSMGRCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_SYSMGRCOLD_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_SYSMGRCOLD register field value. */
#define ALT_RSTMGR_MISCMODRST_SYSMGRCOLD_SET_MSK    0x00000008
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_SYSMGRCOLD register field value. */
#define ALT_RSTMGR_MISCMODRST_SYSMGRCOLD_CLR_MSK    0xfffffff7
/* The reset value of the ALT_RSTMGR_MISCMODRST_SYSMGRCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_SYSMGRCOLD_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_SYSMGRCOLD field value from a register. */
#define ALT_RSTMGR_MISCMODRST_SYSMGRCOLD_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_RSTMGR_MISCMODRST_SYSMGRCOLD register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_SYSMGRCOLD_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : FPGA Manager - fpgamgr
 * 
 * Resets FPGA Manager
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_FPGAMGR register field. */
#define ALT_RSTMGR_MISCMODRST_FPGAMGR_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_FPGAMGR register field. */
#define ALT_RSTMGR_MISCMODRST_FPGAMGR_MSB        4
/* The width in bits of the ALT_RSTMGR_MISCMODRST_FPGAMGR register field. */
#define ALT_RSTMGR_MISCMODRST_FPGAMGR_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_FPGAMGR register field value. */
#define ALT_RSTMGR_MISCMODRST_FPGAMGR_SET_MSK    0x00000010
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_FPGAMGR register field value. */
#define ALT_RSTMGR_MISCMODRST_FPGAMGR_CLR_MSK    0xffffffef
/* The reset value of the ALT_RSTMGR_MISCMODRST_FPGAMGR register field. */
#define ALT_RSTMGR_MISCMODRST_FPGAMGR_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_FPGAMGR field value from a register. */
#define ALT_RSTMGR_MISCMODRST_FPGAMGR_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_RSTMGR_MISCMODRST_FPGAMGR register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_FPGAMGR_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : ACP ID Mapper - acpidmap
 * 
 * Resets ACP ID Mapper
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_ACPIDMAP register field. */
#define ALT_RSTMGR_MISCMODRST_ACPIDMAP_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_ACPIDMAP register field. */
#define ALT_RSTMGR_MISCMODRST_ACPIDMAP_MSB        5
/* The width in bits of the ALT_RSTMGR_MISCMODRST_ACPIDMAP register field. */
#define ALT_RSTMGR_MISCMODRST_ACPIDMAP_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_ACPIDMAP register field value. */
#define ALT_RSTMGR_MISCMODRST_ACPIDMAP_SET_MSK    0x00000020
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_ACPIDMAP register field value. */
#define ALT_RSTMGR_MISCMODRST_ACPIDMAP_CLR_MSK    0xffffffdf
/* The reset value of the ALT_RSTMGR_MISCMODRST_ACPIDMAP register field. */
#define ALT_RSTMGR_MISCMODRST_ACPIDMAP_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_ACPIDMAP field value from a register. */
#define ALT_RSTMGR_MISCMODRST_ACPIDMAP_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_RSTMGR_MISCMODRST_ACPIDMAP register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_ACPIDMAP_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : HPS to FPGA Core (Cold or Warm) - s2f
 * 
 * Resets logic in FPGA core that doesn't differentiate between HPS cold and warm
 * resets (h2f_rst_n = 1)
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_S2F register field. */
#define ALT_RSTMGR_MISCMODRST_S2F_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_S2F register field. */
#define ALT_RSTMGR_MISCMODRST_S2F_MSB        6
/* The width in bits of the ALT_RSTMGR_MISCMODRST_S2F register field. */
#define ALT_RSTMGR_MISCMODRST_S2F_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_S2F register field value. */
#define ALT_RSTMGR_MISCMODRST_S2F_SET_MSK    0x00000040
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_S2F register field value. */
#define ALT_RSTMGR_MISCMODRST_S2F_CLR_MSK    0xffffffbf
/* The reset value of the ALT_RSTMGR_MISCMODRST_S2F register field. */
#define ALT_RSTMGR_MISCMODRST_S2F_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_S2F field value from a register. */
#define ALT_RSTMGR_MISCMODRST_S2F_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_RSTMGR_MISCMODRST_S2F register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_S2F_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : HPS to FPGA Core (Cold-only) - s2fcold
 * 
 * Resets logic in FPGA core that is only reset by a cold reset (ignores warm
 * reset) (h2f_cold_rst_n = 1)
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_S2FCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_S2FCOLD_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_S2FCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_S2FCOLD_MSB        7
/* The width in bits of the ALT_RSTMGR_MISCMODRST_S2FCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_S2FCOLD_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_S2FCOLD register field value. */
#define ALT_RSTMGR_MISCMODRST_S2FCOLD_SET_MSK    0x00000080
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_S2FCOLD register field value. */
#define ALT_RSTMGR_MISCMODRST_S2FCOLD_CLR_MSK    0xffffff7f
/* The reset value of the ALT_RSTMGR_MISCMODRST_S2FCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_S2FCOLD_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_S2FCOLD field value from a register. */
#define ALT_RSTMGR_MISCMODRST_S2FCOLD_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_RSTMGR_MISCMODRST_S2FCOLD register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_S2FCOLD_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : nRST Pin - nrstpin
 * 
 * Pulls nRST pin low
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_NRSTPIN register field. */
#define ALT_RSTMGR_MISCMODRST_NRSTPIN_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_NRSTPIN register field. */
#define ALT_RSTMGR_MISCMODRST_NRSTPIN_MSB        8
/* The width in bits of the ALT_RSTMGR_MISCMODRST_NRSTPIN register field. */
#define ALT_RSTMGR_MISCMODRST_NRSTPIN_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_NRSTPIN register field value. */
#define ALT_RSTMGR_MISCMODRST_NRSTPIN_SET_MSK    0x00000100
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_NRSTPIN register field value. */
#define ALT_RSTMGR_MISCMODRST_NRSTPIN_CLR_MSK    0xfffffeff
/* The reset value of the ALT_RSTMGR_MISCMODRST_NRSTPIN register field. */
#define ALT_RSTMGR_MISCMODRST_NRSTPIN_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_NRSTPIN field value from a register. */
#define ALT_RSTMGR_MISCMODRST_NRSTPIN_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_RSTMGR_MISCMODRST_NRSTPIN register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_NRSTPIN_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Timestamp - timestampcold
 * 
 * Resets debug timestamp to 0 (cold reset only)
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_TSCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_TSCOLD_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_TSCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_TSCOLD_MSB        9
/* The width in bits of the ALT_RSTMGR_MISCMODRST_TSCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_TSCOLD_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_TSCOLD register field value. */
#define ALT_RSTMGR_MISCMODRST_TSCOLD_SET_MSK    0x00000200
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_TSCOLD register field value. */
#define ALT_RSTMGR_MISCMODRST_TSCOLD_CLR_MSK    0xfffffdff
/* The reset value of the ALT_RSTMGR_MISCMODRST_TSCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_TSCOLD_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_TSCOLD field value from a register. */
#define ALT_RSTMGR_MISCMODRST_TSCOLD_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_RSTMGR_MISCMODRST_TSCOLD register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_TSCOLD_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Clock Manager - clkmgrcold
 * 
 * Resets Clock Manager (cold reset only)
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_CLKMGRCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_CLKMGRCOLD_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_CLKMGRCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_CLKMGRCOLD_MSB        10
/* The width in bits of the ALT_RSTMGR_MISCMODRST_CLKMGRCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_CLKMGRCOLD_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_CLKMGRCOLD register field value. */
#define ALT_RSTMGR_MISCMODRST_CLKMGRCOLD_SET_MSK    0x00000400
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_CLKMGRCOLD register field value. */
#define ALT_RSTMGR_MISCMODRST_CLKMGRCOLD_CLR_MSK    0xfffffbff
/* The reset value of the ALT_RSTMGR_MISCMODRST_CLKMGRCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_CLKMGRCOLD_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_CLKMGRCOLD field value from a register. */
#define ALT_RSTMGR_MISCMODRST_CLKMGRCOLD_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_RSTMGR_MISCMODRST_CLKMGRCOLD register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_CLKMGRCOLD_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Scan Manager - scanmgr
 * 
 * Resets Scan Manager
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_SCANMGR register field. */
#define ALT_RSTMGR_MISCMODRST_SCANMGR_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_SCANMGR register field. */
#define ALT_RSTMGR_MISCMODRST_SCANMGR_MSB        11
/* The width in bits of the ALT_RSTMGR_MISCMODRST_SCANMGR register field. */
#define ALT_RSTMGR_MISCMODRST_SCANMGR_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_SCANMGR register field value. */
#define ALT_RSTMGR_MISCMODRST_SCANMGR_SET_MSK    0x00000800
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_SCANMGR register field value. */
#define ALT_RSTMGR_MISCMODRST_SCANMGR_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_RSTMGR_MISCMODRST_SCANMGR register field. */
#define ALT_RSTMGR_MISCMODRST_SCANMGR_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_SCANMGR field value from a register. */
#define ALT_RSTMGR_MISCMODRST_SCANMGR_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_RSTMGR_MISCMODRST_SCANMGR register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_SCANMGR_SET(value) (((value) << 11) & 0x00000800)

/*
 * Field : Freeze Controller - frzctrlcold
 * 
 * Resets Freeze Controller in System Manager (cold reset only)
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_FRZCTLCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_FRZCTLCOLD_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_FRZCTLCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_FRZCTLCOLD_MSB        12
/* The width in bits of the ALT_RSTMGR_MISCMODRST_FRZCTLCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_FRZCTLCOLD_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_FRZCTLCOLD register field value. */
#define ALT_RSTMGR_MISCMODRST_FRZCTLCOLD_SET_MSK    0x00001000
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_FRZCTLCOLD register field value. */
#define ALT_RSTMGR_MISCMODRST_FRZCTLCOLD_CLR_MSK    0xffffefff
/* The reset value of the ALT_RSTMGR_MISCMODRST_FRZCTLCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_FRZCTLCOLD_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_FRZCTLCOLD field value from a register. */
#define ALT_RSTMGR_MISCMODRST_FRZCTLCOLD_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_RSTMGR_MISCMODRST_FRZCTLCOLD register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_FRZCTLCOLD_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : System/Debug - sysdbg
 * 
 * Resets logic that spans the system and debug domains.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_SYSDBG register field. */
#define ALT_RSTMGR_MISCMODRST_SYSDBG_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_SYSDBG register field. */
#define ALT_RSTMGR_MISCMODRST_SYSDBG_MSB        13
/* The width in bits of the ALT_RSTMGR_MISCMODRST_SYSDBG register field. */
#define ALT_RSTMGR_MISCMODRST_SYSDBG_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_SYSDBG register field value. */
#define ALT_RSTMGR_MISCMODRST_SYSDBG_SET_MSK    0x00002000
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_SYSDBG register field value. */
#define ALT_RSTMGR_MISCMODRST_SYSDBG_CLR_MSK    0xffffdfff
/* The reset value of the ALT_RSTMGR_MISCMODRST_SYSDBG register field. */
#define ALT_RSTMGR_MISCMODRST_SYSDBG_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_SYSDBG field value from a register. */
#define ALT_RSTMGR_MISCMODRST_SYSDBG_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_RSTMGR_MISCMODRST_SYSDBG register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_SYSDBG_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : Debug - dbg
 * 
 * Resets logic located only in the debug domain.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_DBG register field. */
#define ALT_RSTMGR_MISCMODRST_DBG_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_DBG register field. */
#define ALT_RSTMGR_MISCMODRST_DBG_MSB        14
/* The width in bits of the ALT_RSTMGR_MISCMODRST_DBG register field. */
#define ALT_RSTMGR_MISCMODRST_DBG_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_DBG register field value. */
#define ALT_RSTMGR_MISCMODRST_DBG_SET_MSK    0x00004000
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_DBG register field value. */
#define ALT_RSTMGR_MISCMODRST_DBG_CLR_MSK    0xffffbfff
/* The reset value of the ALT_RSTMGR_MISCMODRST_DBG register field. */
#define ALT_RSTMGR_MISCMODRST_DBG_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_DBG field value from a register. */
#define ALT_RSTMGR_MISCMODRST_DBG_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_RSTMGR_MISCMODRST_DBG register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_DBG_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : TAP Controller - tapcold
 * 
 * Resets portion of DAP JTAG TAP controller no reset by a debug probe reset (i.e.
 * nTRST pin).  Cold reset only.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_TAPCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_TAPCOLD_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_TAPCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_TAPCOLD_MSB        15
/* The width in bits of the ALT_RSTMGR_MISCMODRST_TAPCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_TAPCOLD_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_TAPCOLD register field value. */
#define ALT_RSTMGR_MISCMODRST_TAPCOLD_SET_MSK    0x00008000
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_TAPCOLD register field value. */
#define ALT_RSTMGR_MISCMODRST_TAPCOLD_CLR_MSK    0xffff7fff
/* The reset value of the ALT_RSTMGR_MISCMODRST_TAPCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_TAPCOLD_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_TAPCOLD field value from a register. */
#define ALT_RSTMGR_MISCMODRST_TAPCOLD_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_RSTMGR_MISCMODRST_TAPCOLD register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_TAPCOLD_SET(value) (((value) << 15) & 0x00008000)

/*
 * Field : SDRAM Controller Subsystem Cold Reset - sdrcold
 * 
 * Resets logic in SDRAM Controller Subsystem affected only by a cold reset.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_RSTMGR_MISCMODRST_SDRCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_SDRCOLD_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_RSTMGR_MISCMODRST_SDRCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_SDRCOLD_MSB        16
/* The width in bits of the ALT_RSTMGR_MISCMODRST_SDRCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_SDRCOLD_WIDTH      1
/* The mask used to set the ALT_RSTMGR_MISCMODRST_SDRCOLD register field value. */
#define ALT_RSTMGR_MISCMODRST_SDRCOLD_SET_MSK    0x00010000
/* The mask used to clear the ALT_RSTMGR_MISCMODRST_SDRCOLD register field value. */
#define ALT_RSTMGR_MISCMODRST_SDRCOLD_CLR_MSK    0xfffeffff
/* The reset value of the ALT_RSTMGR_MISCMODRST_SDRCOLD register field. */
#define ALT_RSTMGR_MISCMODRST_SDRCOLD_RESET      0x0
/* Extracts the ALT_RSTMGR_MISCMODRST_SDRCOLD field value from a register. */
#define ALT_RSTMGR_MISCMODRST_SDRCOLD_GET(value) (((value) & 0x00010000) >> 16)
/* Produces a ALT_RSTMGR_MISCMODRST_SDRCOLD register field value suitable for setting the register. */
#define ALT_RSTMGR_MISCMODRST_SDRCOLD_SET(value) (((value) << 16) & 0x00010000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_RSTMGR_MISCMODRST.
 */
struct ALT_RSTMGR_MISCMODRST_s
{
    uint32_t  rom           :  1;  /* Boot ROM */
    uint32_t  ocram         :  1;  /* On-chip RAM */
    uint32_t  sysmgr        :  1;  /* System Manager (Cold or Warm) */
    uint32_t  sysmgrcold    :  1;  /* System Manager (Cold-only) */
    uint32_t  fpgamgr       :  1;  /* FPGA Manager */
    uint32_t  acpidmap      :  1;  /* ACP ID Mapper */
    uint32_t  s2f           :  1;  /* HPS to FPGA Core (Cold or Warm) */
    uint32_t  s2fcold       :  1;  /* HPS to FPGA Core (Cold-only) */
    uint32_t  nrstpin       :  1;  /* nRST Pin */
    uint32_t  timestampcold :  1;  /* Timestamp */
    uint32_t  clkmgrcold    :  1;  /* Clock Manager */
    uint32_t  scanmgr       :  1;  /* Scan Manager */
    uint32_t  frzctrlcold   :  1;  /* Freeze Controller */
    uint32_t  sysdbg        :  1;  /* System/Debug */
    uint32_t  dbg           :  1;  /* Debug */
    uint32_t  tapcold       :  1;  /* TAP Controller */
    uint32_t  sdrcold       :  1;  /* SDRAM Controller Subsystem Cold Reset */
    uint32_t                : 15;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_RSTMGR_MISCMODRST. */
typedef volatile struct ALT_RSTMGR_MISCMODRST_s  ALT_RSTMGR_MISCMODRST_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_RSTMGR_MISCMODRST register from the beginning of the component. */
#define ALT_RSTMGR_MISCMODRST_OFST        0x20

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_RSTMGR.
 */
struct ALT_RSTMGR_s
{
    volatile ALT_RSTMGR_STAT_t        stat;                 /* ALT_RSTMGR_STAT */
    volatile ALT_RSTMGR_CTL_t         ctrl;                 /* ALT_RSTMGR_CTL */
    volatile ALT_RSTMGR_COUNTS_t      counts;               /* ALT_RSTMGR_COUNTS */
    volatile uint32_t                 _pad_0xc_0xf;         /* *UNDEFINED* */
    volatile ALT_RSTMGR_MPUMODRST_t   mpumodrst;            /* ALT_RSTMGR_MPUMODRST */
    volatile ALT_RSTMGR_PERMODRST_t   permodrst;            /* ALT_RSTMGR_PERMODRST */
    volatile ALT_RSTMGR_PER2MODRST_t  per2modrst;           /* ALT_RSTMGR_PER2MODRST */
    volatile ALT_RSTMGR_BRGMODRST_t   brgmodrst;            /* ALT_RSTMGR_BRGMODRST */
    volatile ALT_RSTMGR_MISCMODRST_t  miscmodrst;           /* ALT_RSTMGR_MISCMODRST */
    volatile uint32_t                 _pad_0x24_0x100[55];  /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_RSTMGR. */
typedef volatile struct ALT_RSTMGR_s  ALT_RSTMGR_t;
/* The struct declaration for the raw register contents of register group ALT_RSTMGR. */
struct ALT_RSTMGR_raw_s
{
    volatile uint32_t  stat;                 /* ALT_RSTMGR_STAT */
    volatile uint32_t  ctrl;                 /* ALT_RSTMGR_CTL */
    volatile uint32_t  counts;               /* ALT_RSTMGR_COUNTS */
    volatile uint32_t  _pad_0xc_0xf;         /* *UNDEFINED* */
    volatile uint32_t  mpumodrst;            /* ALT_RSTMGR_MPUMODRST */
    volatile uint32_t  permodrst;            /* ALT_RSTMGR_PERMODRST */
    volatile uint32_t  per2modrst;           /* ALT_RSTMGR_PER2MODRST */
    volatile uint32_t  brgmodrst;            /* ALT_RSTMGR_BRGMODRST */
    volatile uint32_t  miscmodrst;           /* ALT_RSTMGR_MISCMODRST */
    volatile uint32_t  _pad_0x24_0x100[55];  /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_RSTMGR. */
typedef volatile struct ALT_RSTMGR_raw_s  ALT_RSTMGR_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_RSTMGR_H__ */

