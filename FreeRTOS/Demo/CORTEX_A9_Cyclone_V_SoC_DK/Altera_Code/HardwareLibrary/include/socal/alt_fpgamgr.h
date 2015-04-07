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

/* Altera - ALT_FPGAMGR */

#ifndef __ALTERA_ALT_FPGAMGR_H__
#define __ALTERA_ALT_FPGAMGR_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : FPGA Manager Module - ALT_FPGAMGR
 * FPGA Manager Module
 * 
 * Registers in the FPGA Manager module accessible via its APB slave
 * 
 */
/*
 * Register : Status Register - stat
 * 
 * Provides status fields for software for the FPGA Manager.
 * 
 * The Mode field tells software what configuration phase the FPGA currently is in.
 * For regular configuration through the PINs or through the HPS, these states map
 * directly to customer configuration documentation.
 * 
 * For Configuration Via PCI Express (CVP), the IOCSR configuration is done through
 * the PINS or through HPS.  Then the complete configuration is done through the
 * PCI Express Bus.   When CVP is being done, InitPhase indicates only IOCSR
 * configuration has completed.  CVP_CONF_DONE is available in the CB Monitor for
 * observation by software.
 * 
 * The MSEL field provides a read only register for software to read the MSEL value
 * driven from the external pins.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [2:0]  | RW     | 0x5   | Mode       
 *  [7:3]  | R      | 0x8   | MSEL       
 *  [31:8] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Mode - mode
 * 
 * Reports FPGA state
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                                 
 * :---------------------------------|:------|:---------------------------------------------
 *  ALT_FPGAMGR_STAT_MOD_E_FPGAOFF   | 0x0   | FPGA Powered Off                            
 *  ALT_FPGAMGR_STAT_MOD_E_RSTPHASE  | 0x1   | FPGA in Reset Phase                         
 *  ALT_FPGAMGR_STAT_MOD_E_CFGPHASE  | 0x2   | FPGA in Configuration Phase                 
 *  ALT_FPGAMGR_STAT_MOD_E_INITPHASE | 0x3   | FPGA in Initialization Phase. In CVP        
 * :                                 |       | configuration, this state indicates IO      
 * :                                 |       | configuration has completed.                
 *  ALT_FPGAMGR_STAT_MOD_E_USERMOD   | 0x4   | FPGA in User Mode                           
 *  ALT_FPGAMGR_STAT_MOD_E_UNKNOWN   | 0x5   | FPGA state has not yet been determined. This
 * :                                 |       | only occurs briefly after reset.            
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MOD
 * 
 * FPGA Powered Off
 */
#define ALT_FPGAMGR_STAT_MOD_E_FPGAOFF      0x0
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MOD
 * 
 * FPGA in Reset Phase
 */
#define ALT_FPGAMGR_STAT_MOD_E_RSTPHASE     0x1
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MOD
 * 
 * FPGA in Configuration Phase
 */
#define ALT_FPGAMGR_STAT_MOD_E_CFGPHASE     0x2
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MOD
 * 
 * FPGA in Initialization Phase. In CVP configuration, this state indicates IO
 * configuration has completed.
 */
#define ALT_FPGAMGR_STAT_MOD_E_INITPHASE    0x3
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MOD
 * 
 * FPGA in User Mode
 */
#define ALT_FPGAMGR_STAT_MOD_E_USERMOD      0x4
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MOD
 * 
 * FPGA state has not yet been determined. This only occurs briefly after reset.
 */
#define ALT_FPGAMGR_STAT_MOD_E_UNKNOWN      0x5

/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_STAT_MOD register field. */
#define ALT_FPGAMGR_STAT_MOD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_STAT_MOD register field. */
#define ALT_FPGAMGR_STAT_MOD_MSB        2
/* The width in bits of the ALT_FPGAMGR_STAT_MOD register field. */
#define ALT_FPGAMGR_STAT_MOD_WIDTH      3
/* The mask used to set the ALT_FPGAMGR_STAT_MOD register field value. */
#define ALT_FPGAMGR_STAT_MOD_SET_MSK    0x00000007
/* The mask used to clear the ALT_FPGAMGR_STAT_MOD register field value. */
#define ALT_FPGAMGR_STAT_MOD_CLR_MSK    0xfffffff8
/* The reset value of the ALT_FPGAMGR_STAT_MOD register field. */
#define ALT_FPGAMGR_STAT_MOD_RESET      0x5
/* Extracts the ALT_FPGAMGR_STAT_MOD field value from a register. */
#define ALT_FPGAMGR_STAT_MOD_GET(value) (((value) & 0x00000007) >> 0)
/* Produces a ALT_FPGAMGR_STAT_MOD register field value suitable for setting the register. */
#define ALT_FPGAMGR_STAT_MOD_SET(value) (((value) << 0) & 0x00000007)

/*
 * Field : MSEL - msel
 * 
 * This read-only field allows software to observe the MSEL inputs from the device
 * pins. The MSEL pins define the FPGA configuration mode.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                         | Value | Description                                     
 * :---------------------------------------------|:------|:-------------------------------------------------
 *  ALT_FPGAMGR_STAT_MSEL_E_PP16_FAST_NOAES_NODC | 0x0   | 16-bit Passive Parallel with Fast Power on Reset
 * :                                             |       | Delay;  No AES Encryption; No Data Compression. 
 * :                                             |       | CDRATIO must be programmed to x1                
 *  ALT_FPGAMGR_STAT_MSEL_E_PP16_FAST_AES_NODC   | 0x1   | 16-bit Passive Parallel with Fast Power on Reset
 * :                                             |       | Delay; With AES Encryption; No Data Compression.
 * :                                             |       | CDRATIO must be programmed to x4                
 *  ALT_FPGAMGR_STAT_MSEL_E_PP16_FAST_AESOPT_DC  | 0x2   | 16-bit Passive Parallel with Fast Power on Reset
 * :                                             |       | Delay; AES Optional; With Data Compression.     
 * :                                             |       | CDRATIO must be programmed to x8                
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD3                | 0x3   | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_PP16_SLOW_NOAES_NODC | 0x4   | 16-bit Passive Parallel with Slow Power on Reset
 * :                                             |       | Delay;  No AES Encryption; No Data Compression. 
 * :                                             |       | CDRATIO must be programmed to x1                
 *  ALT_FPGAMGR_STAT_MSEL_E_PP16_SLOW_AES_NODC   | 0x5   | 16-bit Passive Parallel with Slow Power on Reset
 * :                                             |       | Delay; With AES Encryption; No Data Compression.
 * :                                             |       | CDRATIO must be programmed to x4                
 *  ALT_FPGAMGR_STAT_MSEL_E_PP16_SLOW_AESOPT_DC  | 0x6   | 16-bit Passive Parallel with Slow Power on Reset
 * :                                             |       | Delay; AES Optional; With Data Compression.     
 * :                                             |       | CDRATIO must be programmed to x8                
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD7                | 0x7   | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_PP32_FAST_NOAES_NODC | 0x8   | 32-bit Passive Parallel with Fast Power on Reset
 * :                                             |       | Delay;  No AES Encryption; No Data Compression. 
 * :                                             |       | CDRATIO must be programmed to x1                
 *  ALT_FPGAMGR_STAT_MSEL_E_PP32_FAST_AES_NODC   | 0x9   | 32-bit Passive Parallel with Fast Power on Reset
 * :                                             |       | Delay; With AES Encryption; No Data Compression.
 * :                                             |       | CDRATIO must be programmed to x4                
 *  ALT_FPGAMGR_STAT_MSEL_E_PP32_FAST_AESOPT_DC  | 0xa   | 32-bit Passive Parallel with Fast Power on Reset
 * :                                             |       | Delay; AES Optional; With Data Compression.     
 * :                                             |       | CDRATIO must be programmed to x8                
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD11               | 0xb   | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_PP32_SLOW_NOAES_NODC | 0xc   | 32-bit Passive Parallel with Slow Power on Reset
 * :                                             |       | Delay;  No AES Encryption; No Data Compression. 
 * :                                             |       | CDRATIO must be programmed to x1                
 *  ALT_FPGAMGR_STAT_MSEL_E_PP32_SLOW_AES_NODC   | 0xd   | 32-bit Passive Parallel with Slow Power on Reset
 * :                                             |       | Delay; With AES Encryption; No Data Compression.
 * :                                             |       | CDRATIO must be programmed to x4                
 *  ALT_FPGAMGR_STAT_MSEL_E_PP32_SLOW_AESOPT_DC  | 0xe   | 32-bit Passive Parallel with Slow Power on Reset
 * :                                             |       | Delay; AES Optional; With Data Compression.     
 * :                                             |       | CDRATIO must be programmed to x8                
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD15               | 0xf   | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD16               | 0x10  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD17               | 0x11  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD18               | 0x12  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD19               | 0x13  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD20               | 0x14  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD21               | 0x15  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD22               | 0x16  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD23               | 0x17  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD24               | 0x18  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD25               | 0x19  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD26               | 0x1a  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD27               | 0x1b  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD28               | 0x1c  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD29               | 0x1d  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD30               | 0x1e  | Reserved                                        
 *  ALT_FPGAMGR_STAT_MSEL_E_RSVD31               | 0x1f  | Reserved                                        
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * 16-bit Passive Parallel with Fast Power on Reset Delay;  No AES Encryption; No
 * Data Compression.
 * 
 * CDRATIO must be programmed to x1
 */
#define ALT_FPGAMGR_STAT_MSEL_E_PP16_FAST_NOAES_NODC    0x0
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * 16-bit Passive Parallel with Fast Power on Reset Delay; With AES Encryption; No
 * Data Compression.
 * 
 * CDRATIO must be programmed to x4
 */
#define ALT_FPGAMGR_STAT_MSEL_E_PP16_FAST_AES_NODC      0x1
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * 16-bit Passive Parallel with Fast Power on Reset Delay; AES Optional; With Data
 * Compression.
 * 
 * CDRATIO must be programmed to x8
 */
#define ALT_FPGAMGR_STAT_MSEL_E_PP16_FAST_AESOPT_DC     0x2
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD3                   0x3
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * 16-bit Passive Parallel with Slow Power on Reset Delay;  No AES Encryption; No
 * Data Compression.
 * 
 * CDRATIO must be programmed to x1
 */
#define ALT_FPGAMGR_STAT_MSEL_E_PP16_SLOW_NOAES_NODC    0x4
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * 16-bit Passive Parallel with Slow Power on Reset Delay; With AES Encryption; No
 * Data Compression.
 * 
 * CDRATIO must be programmed to x4
 */
#define ALT_FPGAMGR_STAT_MSEL_E_PP16_SLOW_AES_NODC      0x5
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * 16-bit Passive Parallel with Slow Power on Reset Delay; AES Optional; With Data
 * Compression.
 * 
 * CDRATIO must be programmed to x8
 */
#define ALT_FPGAMGR_STAT_MSEL_E_PP16_SLOW_AESOPT_DC     0x6
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD7                   0x7
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * 32-bit Passive Parallel with Fast Power on Reset Delay;  No AES Encryption; No
 * Data Compression.
 * 
 * CDRATIO must be programmed to x1
 */
#define ALT_FPGAMGR_STAT_MSEL_E_PP32_FAST_NOAES_NODC    0x8
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * 32-bit Passive Parallel with Fast Power on Reset Delay; With AES Encryption; No
 * Data Compression.
 * 
 * CDRATIO must be programmed to x4
 */
#define ALT_FPGAMGR_STAT_MSEL_E_PP32_FAST_AES_NODC      0x9
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * 32-bit Passive Parallel with Fast Power on Reset Delay; AES Optional; With Data
 * Compression.
 * 
 * CDRATIO must be programmed to x8
 */
#define ALT_FPGAMGR_STAT_MSEL_E_PP32_FAST_AESOPT_DC     0xa
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD11                  0xb
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * 32-bit Passive Parallel with Slow Power on Reset Delay;  No AES Encryption; No
 * Data Compression.
 * 
 * CDRATIO must be programmed to x1
 */
#define ALT_FPGAMGR_STAT_MSEL_E_PP32_SLOW_NOAES_NODC    0xc
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * 32-bit Passive Parallel with Slow Power on Reset Delay; With AES Encryption; No
 * Data Compression.
 * 
 * CDRATIO must be programmed to x4
 */
#define ALT_FPGAMGR_STAT_MSEL_E_PP32_SLOW_AES_NODC      0xd
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * 32-bit Passive Parallel with Slow Power on Reset Delay; AES Optional; With Data
 * Compression.
 * 
 * CDRATIO must be programmed to x8
 */
#define ALT_FPGAMGR_STAT_MSEL_E_PP32_SLOW_AESOPT_DC     0xe
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD15                  0xf
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD16                  0x10
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD17                  0x11
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD18                  0x12
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD19                  0x13
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD20                  0x14
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD21                  0x15
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD22                  0x16
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD23                  0x17
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD24                  0x18
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD25                  0x19
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD26                  0x1a
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD27                  0x1b
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD28                  0x1c
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD29                  0x1d
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD30                  0x1e
/*
 * Enumerated value for register field ALT_FPGAMGR_STAT_MSEL
 * 
 * Reserved
 */
#define ALT_FPGAMGR_STAT_MSEL_E_RSVD31                  0x1f

/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_STAT_MSEL register field. */
#define ALT_FPGAMGR_STAT_MSEL_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_STAT_MSEL register field. */
#define ALT_FPGAMGR_STAT_MSEL_MSB        7
/* The width in bits of the ALT_FPGAMGR_STAT_MSEL register field. */
#define ALT_FPGAMGR_STAT_MSEL_WIDTH      5
/* The mask used to set the ALT_FPGAMGR_STAT_MSEL register field value. */
#define ALT_FPGAMGR_STAT_MSEL_SET_MSK    0x000000f8
/* The mask used to clear the ALT_FPGAMGR_STAT_MSEL register field value. */
#define ALT_FPGAMGR_STAT_MSEL_CLR_MSK    0xffffff07
/* The reset value of the ALT_FPGAMGR_STAT_MSEL register field. */
#define ALT_FPGAMGR_STAT_MSEL_RESET      0x8
/* Extracts the ALT_FPGAMGR_STAT_MSEL field value from a register. */
#define ALT_FPGAMGR_STAT_MSEL_GET(value) (((value) & 0x000000f8) >> 3)
/* Produces a ALT_FPGAMGR_STAT_MSEL register field value suitable for setting the register. */
#define ALT_FPGAMGR_STAT_MSEL_SET(value) (((value) << 3) & 0x000000f8)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_FPGAMGR_STAT.
 */
struct ALT_FPGAMGR_STAT_s
{
    uint32_t        mode :  3;  /* Mode */
    const uint32_t  msel :  5;  /* MSEL */
    uint32_t             : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_FPGAMGR_STAT. */
typedef volatile struct ALT_FPGAMGR_STAT_s  ALT_FPGAMGR_STAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_FPGAMGR_STAT register from the beginning of the component. */
#define ALT_FPGAMGR_STAT_OFST        0x0

/*
 * Register : Control Register - ctrl
 * 
 * Allows HPS to control FPGA configuration.
 * 
 * The NCONFIGPULL, NSTATUSPULL, and CONFDONEPULL fields drive signals to the FPGA
 * Control Block that are logically ORed into their respective pins. These signals
 * are always driven independent of the value of EN. The polarity of the
 * NCONFIGPULL, NSTATUSPULL, and CONFDONEPULL fields is inverted relative to their
 * associated pins.
 * 
 * The MSEL (external pins), CDRATIO and CFGWDTH signals determine the mode of
 * operation for Normal Configuration. For Partial Reconfiguration, CDRATIO is used
 * to set the appropriate clock to data ratio, and CFGWDTH should always be set to
 * 16-bit Passive Parallel.
 * 
 * AXICFGEN is used to enable transfer of configuration data by enabling or
 * disabling DCLK during data transfers.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description             
 * :--------|:-------|:------|:-------------------------
 *  [0]     | RW     | 0x0   | Enable                  
 *  [1]     | RW     | 0x0   | nCE                     
 *  [2]     | RW     | 0x0   | nCONFIG Pull-Down       
 *  [3]     | RW     | 0x0   | nSTATUS Pull-Down       
 *  [4]     | RW     | 0x0   | CONF_DONE Pull-Down     
 *  [5]     | RW     | 0x0   | Partial Reconfiguration 
 *  [7:6]   | RW     | 0x0   | CD Ratio                
 *  [8]     | RW     | 0x0   | AXI Configuration Enable
 *  [9]     | RW     | 0x1   | Configuration Data Width
 *  [31:10] | ???    | 0x0   | *UNDEFINED*             
 * 
 */
/*
 * Field : Enable - en
 * 
 * Controls whether the FPGA configuration pins or HPS FPGA Manager drive
 * configuration inputs to the CB.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description                                    
 * :---------------------------------------|:------|:------------------------------------------------
 *  ALT_FPGAMGR_CTL_EN_E_FPGA_PINS_CTL_CFG | 0x0   | FPGA configuration pins drive configuration    
 * :                                       |       | inputs to the CB. Used when FPGA is configured 
 * :                                       |       | by means other than the HPS.                   
 *  ALT_FPGAMGR_CTL_EN_E_FPGAMGR_CTLS_CFG  | 0x1   | FPGA Manager drives configuration inputs to the
 * :                                       |       | CB. Used when HPS configures the FPGA.         
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_EN
 * 
 * FPGA configuration pins drive configuration inputs to the CB. Used when FPGA is
 * configured by means other than the HPS.
 */
#define ALT_FPGAMGR_CTL_EN_E_FPGA_PINS_CTL_CFG  0x0
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_EN
 * 
 * FPGA Manager drives configuration inputs to the CB. Used when HPS configures the
 * FPGA.
 */
#define ALT_FPGAMGR_CTL_EN_E_FPGAMGR_CTLS_CFG   0x1

/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_CTL_EN register field. */
#define ALT_FPGAMGR_CTL_EN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_CTL_EN register field. */
#define ALT_FPGAMGR_CTL_EN_MSB        0
/* The width in bits of the ALT_FPGAMGR_CTL_EN register field. */
#define ALT_FPGAMGR_CTL_EN_WIDTH      1
/* The mask used to set the ALT_FPGAMGR_CTL_EN register field value. */
#define ALT_FPGAMGR_CTL_EN_SET_MSK    0x00000001
/* The mask used to clear the ALT_FPGAMGR_CTL_EN register field value. */
#define ALT_FPGAMGR_CTL_EN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_FPGAMGR_CTL_EN register field. */
#define ALT_FPGAMGR_CTL_EN_RESET      0x0
/* Extracts the ALT_FPGAMGR_CTL_EN field value from a register. */
#define ALT_FPGAMGR_CTL_EN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_FPGAMGR_CTL_EN register field value suitable for setting the register. */
#define ALT_FPGAMGR_CTL_EN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : nCE - nce
 * 
 * This field drives the active-low Chip Enable (nCE) signal to the CB. It should
 * be set to 0 (configuration enabled) before CTRL.EN is set.
 * 
 * This field only effects the FPGA if CTRL.EN is 1.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description                                    
 * :-------------------------------|:------|:------------------------------------------------
 *  ALT_FPGAMGR_CTL_NCE_E_CFG_END  | 0x0   | Configuration is enabled. The nCE to the CB is 
 * :                               |       | driven to 0.                                   
 *  ALT_FPGAMGR_CTL_NCE_E_CFG_DISD | 0x1   | Configuration is disabled. The nCE to the CB is
 * :                               |       | driven to 1.                                   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_NCE
 * 
 * Configuration is enabled. The nCE to the CB is driven to 0.
 */
#define ALT_FPGAMGR_CTL_NCE_E_CFG_END   0x0
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_NCE
 * 
 * Configuration is disabled. The nCE to the CB is driven to 1.
 */
#define ALT_FPGAMGR_CTL_NCE_E_CFG_DISD  0x1

/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_CTL_NCE register field. */
#define ALT_FPGAMGR_CTL_NCE_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_CTL_NCE register field. */
#define ALT_FPGAMGR_CTL_NCE_MSB        1
/* The width in bits of the ALT_FPGAMGR_CTL_NCE register field. */
#define ALT_FPGAMGR_CTL_NCE_WIDTH      1
/* The mask used to set the ALT_FPGAMGR_CTL_NCE register field value. */
#define ALT_FPGAMGR_CTL_NCE_SET_MSK    0x00000002
/* The mask used to clear the ALT_FPGAMGR_CTL_NCE register field value. */
#define ALT_FPGAMGR_CTL_NCE_CLR_MSK    0xfffffffd
/* The reset value of the ALT_FPGAMGR_CTL_NCE register field. */
#define ALT_FPGAMGR_CTL_NCE_RESET      0x0
/* Extracts the ALT_FPGAMGR_CTL_NCE field value from a register. */
#define ALT_FPGAMGR_CTL_NCE_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_FPGAMGR_CTL_NCE register field value suitable for setting the register. */
#define ALT_FPGAMGR_CTL_NCE_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : nCONFIG Pull-Down - nconfigpull
 * 
 * The nCONFIG input is used to put the FPGA into its reset phase. If the FPGA was
 * configured, its operation stops and it will have to be configured again to start
 * operation.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                     | Value | Description                                     
 * :-----------------------------------------|:------|:-------------------------------------------------
 *  ALT_FPGAMGR_CTL_NCFGPULL_E_DONT_PULLDOWN | 0x0   | Don't pull-down nCONFIG input to the CB.        
 *  ALT_FPGAMGR_CTL_NCFGPULL_E_PULLDOWN      | 0x1   | Pull-down nCONFIG input to the CB. This puts the
 * :                                         |       | FPGA in reset phase and restarts configuration. 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_NCFGPULL
 * 
 * Don't pull-down nCONFIG input to the CB.
 */
#define ALT_FPGAMGR_CTL_NCFGPULL_E_DONT_PULLDOWN    0x0
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_NCFGPULL
 * 
 * Pull-down nCONFIG input to the CB. This puts the FPGA in reset phase and
 * restarts configuration.
 */
#define ALT_FPGAMGR_CTL_NCFGPULL_E_PULLDOWN         0x1

/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_CTL_NCFGPULL register field. */
#define ALT_FPGAMGR_CTL_NCFGPULL_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_CTL_NCFGPULL register field. */
#define ALT_FPGAMGR_CTL_NCFGPULL_MSB        2
/* The width in bits of the ALT_FPGAMGR_CTL_NCFGPULL register field. */
#define ALT_FPGAMGR_CTL_NCFGPULL_WIDTH      1
/* The mask used to set the ALT_FPGAMGR_CTL_NCFGPULL register field value. */
#define ALT_FPGAMGR_CTL_NCFGPULL_SET_MSK    0x00000004
/* The mask used to clear the ALT_FPGAMGR_CTL_NCFGPULL register field value. */
#define ALT_FPGAMGR_CTL_NCFGPULL_CLR_MSK    0xfffffffb
/* The reset value of the ALT_FPGAMGR_CTL_NCFGPULL register field. */
#define ALT_FPGAMGR_CTL_NCFGPULL_RESET      0x0
/* Extracts the ALT_FPGAMGR_CTL_NCFGPULL field value from a register. */
#define ALT_FPGAMGR_CTL_NCFGPULL_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_FPGAMGR_CTL_NCFGPULL register field value suitable for setting the register. */
#define ALT_FPGAMGR_CTL_NCFGPULL_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : nSTATUS Pull-Down - nstatuspull
 * 
 * Pulls down nSTATUS input to the CB
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description                             
 * :------------------------------------------|:------|:-----------------------------------------
 *  ALT_FPGAMGR_CTL_NSTATPULL_E_DONT_PULLDOWN | 0x0   | Don't pull-down nSTATUS input to the CB.
 *  ALT_FPGAMGR_CTL_NSTATPULL_E_PULLDOWN      | 0x1   | Pull-down nSTATUS input to the CB.      
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_NSTATPULL
 * 
 * Don't pull-down nSTATUS input to the CB.
 */
#define ALT_FPGAMGR_CTL_NSTATPULL_E_DONT_PULLDOWN   0x0
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_NSTATPULL
 * 
 * Pull-down nSTATUS input to the CB.
 */
#define ALT_FPGAMGR_CTL_NSTATPULL_E_PULLDOWN        0x1

/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_CTL_NSTATPULL register field. */
#define ALT_FPGAMGR_CTL_NSTATPULL_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_CTL_NSTATPULL register field. */
#define ALT_FPGAMGR_CTL_NSTATPULL_MSB        3
/* The width in bits of the ALT_FPGAMGR_CTL_NSTATPULL register field. */
#define ALT_FPGAMGR_CTL_NSTATPULL_WIDTH      1
/* The mask used to set the ALT_FPGAMGR_CTL_NSTATPULL register field value. */
#define ALT_FPGAMGR_CTL_NSTATPULL_SET_MSK    0x00000008
/* The mask used to clear the ALT_FPGAMGR_CTL_NSTATPULL register field value. */
#define ALT_FPGAMGR_CTL_NSTATPULL_CLR_MSK    0xfffffff7
/* The reset value of the ALT_FPGAMGR_CTL_NSTATPULL register field. */
#define ALT_FPGAMGR_CTL_NSTATPULL_RESET      0x0
/* Extracts the ALT_FPGAMGR_CTL_NSTATPULL field value from a register. */
#define ALT_FPGAMGR_CTL_NSTATPULL_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_FPGAMGR_CTL_NSTATPULL register field value suitable for setting the register. */
#define ALT_FPGAMGR_CTL_NSTATPULL_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : CONF_DONE Pull-Down - confdonepull
 * 
 * Pulls down CONF_DONE input to the CB
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                         | Value | Description                               
 * :---------------------------------------------|:------|:-------------------------------------------
 *  ALT_FPGAMGR_CTL_CONFDONEPULL_E_DONT_PULLDOWN | 0x0   | Don't pull-down CONF_DONE input to the CB.
 *  ALT_FPGAMGR_CTL_CONFDONEPULL_E_PULLDOWN      | 0x1   | Pull-down CONF_DONE input to the CB.      
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_CONFDONEPULL
 * 
 * Don't pull-down CONF_DONE input to the CB.
 */
#define ALT_FPGAMGR_CTL_CONFDONEPULL_E_DONT_PULLDOWN    0x0
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_CONFDONEPULL
 * 
 * Pull-down CONF_DONE input to the CB.
 */
#define ALT_FPGAMGR_CTL_CONFDONEPULL_E_PULLDOWN         0x1

/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_CTL_CONFDONEPULL register field. */
#define ALT_FPGAMGR_CTL_CONFDONEPULL_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_CTL_CONFDONEPULL register field. */
#define ALT_FPGAMGR_CTL_CONFDONEPULL_MSB        4
/* The width in bits of the ALT_FPGAMGR_CTL_CONFDONEPULL register field. */
#define ALT_FPGAMGR_CTL_CONFDONEPULL_WIDTH      1
/* The mask used to set the ALT_FPGAMGR_CTL_CONFDONEPULL register field value. */
#define ALT_FPGAMGR_CTL_CONFDONEPULL_SET_MSK    0x00000010
/* The mask used to clear the ALT_FPGAMGR_CTL_CONFDONEPULL register field value. */
#define ALT_FPGAMGR_CTL_CONFDONEPULL_CLR_MSK    0xffffffef
/* The reset value of the ALT_FPGAMGR_CTL_CONFDONEPULL register field. */
#define ALT_FPGAMGR_CTL_CONFDONEPULL_RESET      0x0
/* Extracts the ALT_FPGAMGR_CTL_CONFDONEPULL field value from a register. */
#define ALT_FPGAMGR_CTL_CONFDONEPULL_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_FPGAMGR_CTL_CONFDONEPULL register field value suitable for setting the register. */
#define ALT_FPGAMGR_CTL_CONFDONEPULL_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Partial Reconfiguration - prreq
 * 
 * This field is used to assert PR_REQUEST to request partial reconfiguration while
 * the FPGA is in User Mode. This field only affects the FPGA if CTRL.EN is 1.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                        
 * :---------------------------------|:------|:------------------------------------
 *  ALT_FPGAMGR_CTL_PRREQ_E_DEASSERT | 0x0   | De-assert PR_REQUEST (driven to 0).
 *  ALT_FPGAMGR_CTL_PRREQ_E_ASSERT   | 0x1   | Assert PR_REQUEST (driven to 1).   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_PRREQ
 * 
 * De-assert PR_REQUEST (driven to 0).
 */
#define ALT_FPGAMGR_CTL_PRREQ_E_DEASSERT    0x0
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_PRREQ
 * 
 * Assert PR_REQUEST (driven to 1).
 */
#define ALT_FPGAMGR_CTL_PRREQ_E_ASSERT      0x1

/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_CTL_PRREQ register field. */
#define ALT_FPGAMGR_CTL_PRREQ_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_CTL_PRREQ register field. */
#define ALT_FPGAMGR_CTL_PRREQ_MSB        5
/* The width in bits of the ALT_FPGAMGR_CTL_PRREQ register field. */
#define ALT_FPGAMGR_CTL_PRREQ_WIDTH      1
/* The mask used to set the ALT_FPGAMGR_CTL_PRREQ register field value. */
#define ALT_FPGAMGR_CTL_PRREQ_SET_MSK    0x00000020
/* The mask used to clear the ALT_FPGAMGR_CTL_PRREQ register field value. */
#define ALT_FPGAMGR_CTL_PRREQ_CLR_MSK    0xffffffdf
/* The reset value of the ALT_FPGAMGR_CTL_PRREQ register field. */
#define ALT_FPGAMGR_CTL_PRREQ_RESET      0x0
/* Extracts the ALT_FPGAMGR_CTL_PRREQ field value from a register. */
#define ALT_FPGAMGR_CTL_PRREQ_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_FPGAMGR_CTL_PRREQ register field value suitable for setting the register. */
#define ALT_FPGAMGR_CTL_PRREQ_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : CD Ratio - cdratio
 * 
 * This field controls the Clock to Data Ratio (CDRATIO) for Normal Configuration
 * and Partial Reconfiguration data transfer from the AXI Slave to the FPGA.
 * 
 * For Normal Configuration, the value in this field must be set to be consistent
 * to the implied CD ratio of the MSEL setting.
 * 
 * For Partial Reconfiguration, the value in this field must be set to the same
 * clock to data ratio in the options bits in the Normal Configuration file.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description 
 * :-----------------------------|:------|:-------------
 *  ALT_FPGAMGR_CTL_CDRATIO_E_X1 | 0x0   | CDRATIO of 1
 *  ALT_FPGAMGR_CTL_CDRATIO_E_X2 | 0x1   | CDRATIO of 2
 *  ALT_FPGAMGR_CTL_CDRATIO_E_X4 | 0x2   | CDRATIO of 4
 *  ALT_FPGAMGR_CTL_CDRATIO_E_X8 | 0x3   | CDRATIO of 8
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_CDRATIO
 * 
 * CDRATIO of 1
 */
#define ALT_FPGAMGR_CTL_CDRATIO_E_X1    0x0
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_CDRATIO
 * 
 * CDRATIO of 2
 */
#define ALT_FPGAMGR_CTL_CDRATIO_E_X2    0x1
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_CDRATIO
 * 
 * CDRATIO of 4
 */
#define ALT_FPGAMGR_CTL_CDRATIO_E_X4    0x2
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_CDRATIO
 * 
 * CDRATIO of 8
 */
#define ALT_FPGAMGR_CTL_CDRATIO_E_X8    0x3

/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_CTL_CDRATIO register field. */
#define ALT_FPGAMGR_CTL_CDRATIO_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_CTL_CDRATIO register field. */
#define ALT_FPGAMGR_CTL_CDRATIO_MSB        7
/* The width in bits of the ALT_FPGAMGR_CTL_CDRATIO register field. */
#define ALT_FPGAMGR_CTL_CDRATIO_WIDTH      2
/* The mask used to set the ALT_FPGAMGR_CTL_CDRATIO register field value. */
#define ALT_FPGAMGR_CTL_CDRATIO_SET_MSK    0x000000c0
/* The mask used to clear the ALT_FPGAMGR_CTL_CDRATIO register field value. */
#define ALT_FPGAMGR_CTL_CDRATIO_CLR_MSK    0xffffff3f
/* The reset value of the ALT_FPGAMGR_CTL_CDRATIO register field. */
#define ALT_FPGAMGR_CTL_CDRATIO_RESET      0x0
/* Extracts the ALT_FPGAMGR_CTL_CDRATIO field value from a register. */
#define ALT_FPGAMGR_CTL_CDRATIO_GET(value) (((value) & 0x000000c0) >> 6)
/* Produces a ALT_FPGAMGR_CTL_CDRATIO register field value suitable for setting the register. */
#define ALT_FPGAMGR_CTL_CDRATIO_SET(value) (((value) << 6) & 0x000000c0)

/*
 * Field : AXI Configuration Enable - axicfgen
 * 
 * There are strict SW initialization steps for configuration, partial
 * configuration and error cases.  When SW is sending configuration files, this bit
 * must be set before the file is transferred on the AXI bus.  This bit enables the
 * DCLK during the AXI configuration data transfers.
 * 
 * Note, the AXI and configuration datapaths remain active irregardless of the
 * state of this bit.   Simply, if the AXI slave is enabled, the DCLK to the CB
 * will be active.   If disabled, the DCLK to the CB will not be active.   So AXI
 * transfers destined to the FPGA Manager when AXIEN is 0, will complete normally
 * from the HPS perspective.
 * 
 * This field only affects the FPGA if CTRL.EN is 1.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description                                 
 * :--------------------------------|:------|:---------------------------------------------
 *  ALT_FPGAMGR_CTL_AXICFGEN_E_DISD | 0x0   | Incoming AXI data transfers will be ignored.
 * :                                |       | DCLK will not toggle during data transfer.  
 *  ALT_FPGAMGR_CTL_AXICFGEN_E_END  | 0x1   | AXI data transfer to CB is active. DCLK will
 * :                                |       | toggle during data transfer.                
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_AXICFGEN
 * 
 * Incoming AXI data transfers will be ignored. DCLK will not toggle during data
 * transfer.
 */
#define ALT_FPGAMGR_CTL_AXICFGEN_E_DISD 0x0
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_AXICFGEN
 * 
 * AXI data transfer to CB is active. DCLK will toggle during data transfer.
 */
#define ALT_FPGAMGR_CTL_AXICFGEN_E_END  0x1

/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_CTL_AXICFGEN register field. */
#define ALT_FPGAMGR_CTL_AXICFGEN_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_CTL_AXICFGEN register field. */
#define ALT_FPGAMGR_CTL_AXICFGEN_MSB        8
/* The width in bits of the ALT_FPGAMGR_CTL_AXICFGEN register field. */
#define ALT_FPGAMGR_CTL_AXICFGEN_WIDTH      1
/* The mask used to set the ALT_FPGAMGR_CTL_AXICFGEN register field value. */
#define ALT_FPGAMGR_CTL_AXICFGEN_SET_MSK    0x00000100
/* The mask used to clear the ALT_FPGAMGR_CTL_AXICFGEN register field value. */
#define ALT_FPGAMGR_CTL_AXICFGEN_CLR_MSK    0xfffffeff
/* The reset value of the ALT_FPGAMGR_CTL_AXICFGEN register field. */
#define ALT_FPGAMGR_CTL_AXICFGEN_RESET      0x0
/* Extracts the ALT_FPGAMGR_CTL_AXICFGEN field value from a register. */
#define ALT_FPGAMGR_CTL_AXICFGEN_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_FPGAMGR_CTL_AXICFGEN register field value suitable for setting the register. */
#define ALT_FPGAMGR_CTL_AXICFGEN_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Configuration Data Width - cfgwdth
 * 
 * This field determines the Configuration Passive Parallel data bus width when HPS
 * configures the FPGA.   Only 32-bit Passive Parallel or 16-bit Passive Parallel
 * are supported.
 * 
 * When HPS does Normal Configuration, configuration should use 32-bit Passive
 * Parallel Mode.   The external pins MSEL must be set appropriately for the
 * configuration selected.
 * 
 * For Partial Reconfiguration, 16-bit Passive Parallel must be used.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description            
 * :--------------------------------|:------|:------------------------
 *  ALT_FPGAMGR_CTL_CFGWDTH_E_PPX16 | 0x0   | 16-bit Passive Parallel
 *  ALT_FPGAMGR_CTL_CFGWDTH_E_PPX32 | 0x1   | 32-bit Passive Parallel
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_CFGWDTH
 * 
 * 16-bit Passive Parallel
 */
#define ALT_FPGAMGR_CTL_CFGWDTH_E_PPX16 0x0
/*
 * Enumerated value for register field ALT_FPGAMGR_CTL_CFGWDTH
 * 
 * 32-bit Passive Parallel
 */
#define ALT_FPGAMGR_CTL_CFGWDTH_E_PPX32 0x1

/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_CTL_CFGWDTH register field. */
#define ALT_FPGAMGR_CTL_CFGWDTH_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_CTL_CFGWDTH register field. */
#define ALT_FPGAMGR_CTL_CFGWDTH_MSB        9
/* The width in bits of the ALT_FPGAMGR_CTL_CFGWDTH register field. */
#define ALT_FPGAMGR_CTL_CFGWDTH_WIDTH      1
/* The mask used to set the ALT_FPGAMGR_CTL_CFGWDTH register field value. */
#define ALT_FPGAMGR_CTL_CFGWDTH_SET_MSK    0x00000200
/* The mask used to clear the ALT_FPGAMGR_CTL_CFGWDTH register field value. */
#define ALT_FPGAMGR_CTL_CFGWDTH_CLR_MSK    0xfffffdff
/* The reset value of the ALT_FPGAMGR_CTL_CFGWDTH register field. */
#define ALT_FPGAMGR_CTL_CFGWDTH_RESET      0x1
/* Extracts the ALT_FPGAMGR_CTL_CFGWDTH field value from a register. */
#define ALT_FPGAMGR_CTL_CFGWDTH_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_FPGAMGR_CTL_CFGWDTH register field value suitable for setting the register. */
#define ALT_FPGAMGR_CTL_CFGWDTH_SET(value) (((value) << 9) & 0x00000200)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_FPGAMGR_CTL.
 */
struct ALT_FPGAMGR_CTL_s
{
    uint32_t  en           :  1;  /* Enable */
    uint32_t  nce          :  1;  /* nCE */
    uint32_t  nconfigpull  :  1;  /* nCONFIG Pull-Down */
    uint32_t  nstatuspull  :  1;  /* nSTATUS Pull-Down */
    uint32_t  confdonepull :  1;  /* CONF_DONE Pull-Down */
    uint32_t  prreq        :  1;  /* Partial Reconfiguration */
    uint32_t  cdratio      :  2;  /* CD Ratio */
    uint32_t  axicfgen     :  1;  /* AXI Configuration Enable */
    uint32_t  cfgwdth      :  1;  /* Configuration Data Width */
    uint32_t               : 22;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_FPGAMGR_CTL. */
typedef volatile struct ALT_FPGAMGR_CTL_s  ALT_FPGAMGR_CTL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_FPGAMGR_CTL register from the beginning of the component. */
#define ALT_FPGAMGR_CTL_OFST        0x4

/*
 * Register : DCLK Count Register - dclkcnt
 * 
 * Used to give software control in enabling DCLK at any time.
 * 
 * SW will need control of the DCLK in specific configuration and partial
 * reconfiguration initialization steps to send spurious DCLKs required by the CB.
 * SW takes ownership for DCLK during normal configuration, partial
 * reconfiguration, error scenerio handshakes including SEU CRC error during
 * partial reconfiguration, SW early abort of partial reconfiguration, and
 * initializatin phase DCLK driving.
 * 
 * During initialization phase, a configuration image loaded into the FPGA can
 * request that DCLK be used as the initialization phase clock instead of the
 * default internal oscillator or optionally the CLKUSR pin. In the case that DCLK
 * is requested, the DCLKCNT register is used by software to control DCLK during
 * the initialization phase.
 * 
 * Software should poll the DCLKSTAT.DCNTDONE write one to clear register to be set
 * when the correct number of DCLKs have completed.  Software should clear
 * DCLKSTAT.DCNTDONE before writing to the DCLKCNT register again.
 * 
 * This field only affects the FPGA if CTRL.EN is 1.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [31:0] | RW     | 0x0   | Count      
 * 
 */
/*
 * Field : Count - cnt
 * 
 * Controls DCLK counter.
 * 
 * Software writes a non-zero value into CNT and the FPGA Manager generates the
 * specified number of DCLK pulses and decrements COUNT.  This register will read
 * back the original value written by software.
 * 
 * Software can write CNT at any time.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_DCLKCNT_CNT register field. */
#define ALT_FPGAMGR_DCLKCNT_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_DCLKCNT_CNT register field. */
#define ALT_FPGAMGR_DCLKCNT_CNT_MSB        31
/* The width in bits of the ALT_FPGAMGR_DCLKCNT_CNT register field. */
#define ALT_FPGAMGR_DCLKCNT_CNT_WIDTH      32
/* The mask used to set the ALT_FPGAMGR_DCLKCNT_CNT register field value. */
#define ALT_FPGAMGR_DCLKCNT_CNT_SET_MSK    0xffffffff
/* The mask used to clear the ALT_FPGAMGR_DCLKCNT_CNT register field value. */
#define ALT_FPGAMGR_DCLKCNT_CNT_CLR_MSK    0x00000000
/* The reset value of the ALT_FPGAMGR_DCLKCNT_CNT register field. */
#define ALT_FPGAMGR_DCLKCNT_CNT_RESET      0x0
/* Extracts the ALT_FPGAMGR_DCLKCNT_CNT field value from a register. */
#define ALT_FPGAMGR_DCLKCNT_CNT_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_FPGAMGR_DCLKCNT_CNT register field value suitable for setting the register. */
#define ALT_FPGAMGR_DCLKCNT_CNT_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_FPGAMGR_DCLKCNT.
 */
struct ALT_FPGAMGR_DCLKCNT_s
{
    uint32_t  cnt : 32;  /* Count */
};

/* The typedef declaration for register ALT_FPGAMGR_DCLKCNT. */
typedef volatile struct ALT_FPGAMGR_DCLKCNT_s  ALT_FPGAMGR_DCLKCNT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_FPGAMGR_DCLKCNT register from the beginning of the component. */
#define ALT_FPGAMGR_DCLKCNT_OFST        0x8

/*
 * Register : DCLK Status Register - dclkstat
 * 
 * This write one to clear register indicates that the DCLKCNT has counted down to
 * zero.  The DCLKCNT is used by software to drive spurious DCLKs to the FPGA.
 * Software will poll this bit after writing DCLKCNT to know when all of the DCLKs
 * have been sent.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description    
 * :-------|:-------|:------|:----------------
 *  [0]    | RW     | 0x0   | DCLK Count Done
 *  [31:1] | ???    | 0x0   | *UNDEFINED*    
 * 
 */
/*
 * Field : DCLK Count Done - dcntdone
 * 
 * This bit is write one to clear.   This bit gets set after the DCLKCNT has
 * counted down to zero (transition from 1 to 0).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                    | Value | Description                    
 * :----------------------------------------|:------|:--------------------------------
 *  ALT_FPGAMGR_DCLKSTAT_DCNTDONE_E_NOTDONE | 0x0   | DCLKCNT is still counting down.
 *  ALT_FPGAMGR_DCLKSTAT_DCNTDONE_E_DONE    | 0x1   | DCLKCNT is done counting down. 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_FPGAMGR_DCLKSTAT_DCNTDONE
 * 
 * DCLKCNT is still counting down.
 */
#define ALT_FPGAMGR_DCLKSTAT_DCNTDONE_E_NOTDONE 0x0
/*
 * Enumerated value for register field ALT_FPGAMGR_DCLKSTAT_DCNTDONE
 * 
 * DCLKCNT is done counting down.
 */
#define ALT_FPGAMGR_DCLKSTAT_DCNTDONE_E_DONE    0x1

/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_DCLKSTAT_DCNTDONE register field. */
#define ALT_FPGAMGR_DCLKSTAT_DCNTDONE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_DCLKSTAT_DCNTDONE register field. */
#define ALT_FPGAMGR_DCLKSTAT_DCNTDONE_MSB        0
/* The width in bits of the ALT_FPGAMGR_DCLKSTAT_DCNTDONE register field. */
#define ALT_FPGAMGR_DCLKSTAT_DCNTDONE_WIDTH      1
/* The mask used to set the ALT_FPGAMGR_DCLKSTAT_DCNTDONE register field value. */
#define ALT_FPGAMGR_DCLKSTAT_DCNTDONE_SET_MSK    0x00000001
/* The mask used to clear the ALT_FPGAMGR_DCLKSTAT_DCNTDONE register field value. */
#define ALT_FPGAMGR_DCLKSTAT_DCNTDONE_CLR_MSK    0xfffffffe
/* The reset value of the ALT_FPGAMGR_DCLKSTAT_DCNTDONE register field. */
#define ALT_FPGAMGR_DCLKSTAT_DCNTDONE_RESET      0x0
/* Extracts the ALT_FPGAMGR_DCLKSTAT_DCNTDONE field value from a register. */
#define ALT_FPGAMGR_DCLKSTAT_DCNTDONE_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_FPGAMGR_DCLKSTAT_DCNTDONE register field value suitable for setting the register. */
#define ALT_FPGAMGR_DCLKSTAT_DCNTDONE_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_FPGAMGR_DCLKSTAT.
 */
struct ALT_FPGAMGR_DCLKSTAT_s
{
    uint32_t  dcntdone :  1;  /* DCLK Count Done */
    uint32_t           : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_FPGAMGR_DCLKSTAT. */
typedef volatile struct ALT_FPGAMGR_DCLKSTAT_s  ALT_FPGAMGR_DCLKSTAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_FPGAMGR_DCLKSTAT register from the beginning of the component. */
#define ALT_FPGAMGR_DCLKSTAT_OFST        0xc

/*
 * Register : General-Purpose Output Register - gpo
 * 
 * Provides a low-latency, low-performance, and simple way to drive general-purpose
 * signals to the FPGA fabric.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [31:0] | RW     | 0x0   | Value      
 * 
 */
/*
 * Field : Value - value
 * 
 * Drives h2f_gp[31:0] with specified value. When read, returns the current value
 * being driven to the FPGA fabric.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_GPO_VALUE register field. */
#define ALT_FPGAMGR_GPO_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_GPO_VALUE register field. */
#define ALT_FPGAMGR_GPO_VALUE_MSB        31
/* The width in bits of the ALT_FPGAMGR_GPO_VALUE register field. */
#define ALT_FPGAMGR_GPO_VALUE_WIDTH      32
/* The mask used to set the ALT_FPGAMGR_GPO_VALUE register field value. */
#define ALT_FPGAMGR_GPO_VALUE_SET_MSK    0xffffffff
/* The mask used to clear the ALT_FPGAMGR_GPO_VALUE register field value. */
#define ALT_FPGAMGR_GPO_VALUE_CLR_MSK    0x00000000
/* The reset value of the ALT_FPGAMGR_GPO_VALUE register field. */
#define ALT_FPGAMGR_GPO_VALUE_RESET      0x0
/* Extracts the ALT_FPGAMGR_GPO_VALUE field value from a register. */
#define ALT_FPGAMGR_GPO_VALUE_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_FPGAMGR_GPO_VALUE register field value suitable for setting the register. */
#define ALT_FPGAMGR_GPO_VALUE_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_FPGAMGR_GPO.
 */
struct ALT_FPGAMGR_GPO_s
{
    uint32_t  value : 32;  /* Value */
};

/* The typedef declaration for register ALT_FPGAMGR_GPO. */
typedef volatile struct ALT_FPGAMGR_GPO_s  ALT_FPGAMGR_GPO_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_FPGAMGR_GPO register from the beginning of the component. */
#define ALT_FPGAMGR_GPO_OFST        0x10

/*
 * Register : General-Purpose Input Register - gpi
 * 
 * Provides a low-latency, low-performance, and simple way to read general-purpose
 * signals driven from the FPGA fabric.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description
 * :-------|:-------|:--------|:------------
 *  [31:0] | R      | Unknown | Value      
 * 
 */
/*
 * Field : Value - value
 * 
 * The value being driven from the FPGA fabric on f2h_gp[31:0]. If the FPGA is not
 * in User Mode, the value of this field is undefined.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_GPI_VALUE register field. */
#define ALT_FPGAMGR_GPI_VALUE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_GPI_VALUE register field. */
#define ALT_FPGAMGR_GPI_VALUE_MSB        31
/* The width in bits of the ALT_FPGAMGR_GPI_VALUE register field. */
#define ALT_FPGAMGR_GPI_VALUE_WIDTH      32
/* The mask used to set the ALT_FPGAMGR_GPI_VALUE register field value. */
#define ALT_FPGAMGR_GPI_VALUE_SET_MSK    0xffffffff
/* The mask used to clear the ALT_FPGAMGR_GPI_VALUE register field value. */
#define ALT_FPGAMGR_GPI_VALUE_CLR_MSK    0x00000000
/* The reset value of the ALT_FPGAMGR_GPI_VALUE register field is UNKNOWN. */
#define ALT_FPGAMGR_GPI_VALUE_RESET      0x0
/* Extracts the ALT_FPGAMGR_GPI_VALUE field value from a register. */
#define ALT_FPGAMGR_GPI_VALUE_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_FPGAMGR_GPI_VALUE register field value suitable for setting the register. */
#define ALT_FPGAMGR_GPI_VALUE_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_FPGAMGR_GPI.
 */
struct ALT_FPGAMGR_GPI_s
{
    const uint32_t  value : 32;  /* Value */
};

/* The typedef declaration for register ALT_FPGAMGR_GPI. */
typedef volatile struct ALT_FPGAMGR_GPI_s  ALT_FPGAMGR_GPI_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_FPGAMGR_GPI register from the beginning of the component. */
#define ALT_FPGAMGR_GPI_OFST        0x14

/*
 * Register : Miscellaneous Input Register - misci
 * 
 * Provides a low-latency, low-performance, and simple way to read specific
 * handshaking signals driven from the FPGA fabric.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description              
 * :-------|:-------|:--------|:--------------------------
 *  [0]    | R      | Unknown | Boot From FPGA on Failure
 *  [1]    | R      | Unknown | Boot From FPGA Ready     
 *  [31:2] | ???    | 0x0     | *UNDEFINED*              
 * 
 */
/*
 * Field : Boot From FPGA on Failure - bootFPGAfail
 * 
 * The value of the f2h_boot_from_fpga_on_failure signal from the FPGA fabric. If
 * the FPGA is not in User Mode, the value of this field is undefined.
 * 
 * 1 = Boot ROM will boot from FPGA if boot from normal boot device fails.
 * 
 * 0 = Boot ROM will not boot from FPGA if boot from normal boot device fails.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_MISCI_BOOTFPGAFAIL register field. */
#define ALT_FPGAMGR_MISCI_BOOTFPGAFAIL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_MISCI_BOOTFPGAFAIL register field. */
#define ALT_FPGAMGR_MISCI_BOOTFPGAFAIL_MSB        0
/* The width in bits of the ALT_FPGAMGR_MISCI_BOOTFPGAFAIL register field. */
#define ALT_FPGAMGR_MISCI_BOOTFPGAFAIL_WIDTH      1
/* The mask used to set the ALT_FPGAMGR_MISCI_BOOTFPGAFAIL register field value. */
#define ALT_FPGAMGR_MISCI_BOOTFPGAFAIL_SET_MSK    0x00000001
/* The mask used to clear the ALT_FPGAMGR_MISCI_BOOTFPGAFAIL register field value. */
#define ALT_FPGAMGR_MISCI_BOOTFPGAFAIL_CLR_MSK    0xfffffffe
/* The reset value of the ALT_FPGAMGR_MISCI_BOOTFPGAFAIL register field is UNKNOWN. */
#define ALT_FPGAMGR_MISCI_BOOTFPGAFAIL_RESET      0x0
/* Extracts the ALT_FPGAMGR_MISCI_BOOTFPGAFAIL field value from a register. */
#define ALT_FPGAMGR_MISCI_BOOTFPGAFAIL_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_FPGAMGR_MISCI_BOOTFPGAFAIL register field value suitable for setting the register. */
#define ALT_FPGAMGR_MISCI_BOOTFPGAFAIL_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Boot From FPGA Ready - bootFPGArdy
 * 
 * The value of the f2h_boot_from_fpga_ready signal from the FPGA fabric. If the
 * FPGA is not in User Mode, the value of this field is undefined.
 * 
 * 1 = FPGA fabric is ready to accept AXI master requests from the HPS2FPGA bridge.
 * 
 * 0 = FPGA fabric is not ready (probably still processing a reset).
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_FPGAMGR_MISCI_BOOTFPGARDY register field. */
#define ALT_FPGAMGR_MISCI_BOOTFPGARDY_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_FPGAMGR_MISCI_BOOTFPGARDY register field. */
#define ALT_FPGAMGR_MISCI_BOOTFPGARDY_MSB        1
/* The width in bits of the ALT_FPGAMGR_MISCI_BOOTFPGARDY register field. */
#define ALT_FPGAMGR_MISCI_BOOTFPGARDY_WIDTH      1
/* The mask used to set the ALT_FPGAMGR_MISCI_BOOTFPGARDY register field value. */
#define ALT_FPGAMGR_MISCI_BOOTFPGARDY_SET_MSK    0x00000002
/* The mask used to clear the ALT_FPGAMGR_MISCI_BOOTFPGARDY register field value. */
#define ALT_FPGAMGR_MISCI_BOOTFPGARDY_CLR_MSK    0xfffffffd
/* The reset value of the ALT_FPGAMGR_MISCI_BOOTFPGARDY register field is UNKNOWN. */
#define ALT_FPGAMGR_MISCI_BOOTFPGARDY_RESET      0x0
/* Extracts the ALT_FPGAMGR_MISCI_BOOTFPGARDY field value from a register. */
#define ALT_FPGAMGR_MISCI_BOOTFPGARDY_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_FPGAMGR_MISCI_BOOTFPGARDY register field value suitable for setting the register. */
#define ALT_FPGAMGR_MISCI_BOOTFPGARDY_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_FPGAMGR_MISCI.
 */
struct ALT_FPGAMGR_MISCI_s
{
    const uint32_t  bootFPGAfail :  1;  /* Boot From FPGA on Failure */
    const uint32_t  bootFPGArdy  :  1;  /* Boot From FPGA Ready */
    uint32_t                     : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_FPGAMGR_MISCI. */
typedef volatile struct ALT_FPGAMGR_MISCI_s  ALT_FPGAMGR_MISCI_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_FPGAMGR_MISCI register from the beginning of the component. */
#define ALT_FPGAMGR_MISCI_OFST        0x18

/*
 * Register Group : Configuration Monitor (MON) Registers - ALT_MON
 * Configuration Monitor (MON) Registers
 * 
 * The Configuration Monitor allows software to poll or be interrupted by changes
 * in the FPGA state. The Configuration Monitor is an instantiation of a Synopsys
 * GPIO. Only registers relevant to the MON operation are shown.
 * 
 * The GPIO inputs are connected to the following signals:[list][*]nSTATUS - Driven
 * to 0 by the FPGA in this device if the FPGA is in Reset Phase or if the FPGA
 * detected an error during the Configuration Phase.[*]CONF_DONE - Driven to 0 by
 * the FPGA in this device during the Reset Phase and driven to 1 when the FPGA
 * Configuration Phase is done.[*]INIT_DONE - Driven to 0 by the FPGA in this
 * device during the Configuration Phase and driven to 1 when the FPGA
 * Initialization Phase is done.[*]CRC_ERROR - CRC error indicator. A CRC_ERROR
 * value of 1 indicates that the FPGA detected a CRC error while in User
 * Mode.[*]CVP_CONF_DONE - Configuration via PCIe done indicator. A CVP_CONF_DONE
 * value of 1 indicates that CVP is done.[*]PR_READY - Partial reconfiguration
 * ready indicator. A PR_READY value of 1 indicates that the FPGA is ready to
 * receive partial reconfiguration or external scrubbing data.[*]PR_ERROR - Partial
 * reconfiguration error indicator. A PR_ERROR value of 1 indicates that the FPGA
 * detected an error during partial reconfiguration or external
 * scrubbing.[*]PR_DONE - Partial reconfiguration done indicator. A PR_DONE value
 * of 1 indicates partial reconfiguration or external scrubbing is done.[*]nCONFIG
 * Pin - Value of the nCONFIG pin. This can be pulled-down by the FPGA in this
 * device or logic external to this device connected to the nCONFIG pin. See the
 * description of the nCONFIG field in this register to understand when the FPGA in
 * this device pulls-down the nCONFIG pin. Logic external to this device pulls-down
 * the nCONFIG pin to put the FPGA into the Reset Phase.[*]nSTATUS Pin - Value of
 * the nSTATUS pin. This can be pulled-down by the FPGA in this device or logic
 * external to this device connected to the nSTATUS pin. See the description of the
 * nSTATUS field in this register to understand when the FPGA in this device pulls-
 * down the nSTATUS pin. Logic external to this device pulls-down the nSTATUS pin
 * during Configuration Phase or Initialization Phase if it detected an
 * error.[*]CONF_DONE Pin - Value of the CONF_DONE pin. This can be pulled-down by
 * the FPGA in this device or logic external to this device connected to the
 * CONF_DONE pin. See the description of the CONF_DONE field in this register to
 * understand when the FPGA in this device pulls-down the CONF_DONE pin. See FPGA
 * documentation to determine how logic external to this device drives
 * CONF_DONE.[*]FPGA_POWER_ON - FPGA powered on indicator
 * 
 * [list][*]0 = FPGA portion of device is powered off.[*]1 = FPGA portion of device
 * is powered on.[/list][/list]
 * 
 */
/*
 * Register : Interrupt Enable Register - gpio_inten
 * 
 * Allows each bit of Port A to be configured to generate an interrupt or not.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                           
 * :--------|:-------|:------|:---------------------------------------
 *  [0]     | RW     | 0x0   | Interrupt Enable Field (nSTATUS)      
 *  [1]     | RW     | 0x0   | Interrupt Enable Field (CONF_DONE)    
 *  [2]     | RW     | 0x0   | Interrupt Enable Field (INIT_DONE)    
 *  [3]     | RW     | 0x0   | Interrupt Enable Field (CRC_ERROR)    
 *  [4]     | RW     | 0x0   | Interrupt Enable Field (CVP_CONF_DONE)
 *  [5]     | RW     | 0x0   | Interrupt Enable Field (PR_READY)     
 *  [6]     | RW     | 0x0   | Interrupt Enable Field (PR_ERROR)     
 *  [7]     | RW     | 0x0   | Interrupt Enable Field (PR_DONE)      
 *  [8]     | RW     | 0x0   | Interrupt Enable Field (nCONFIG Pin)  
 *  [9]     | RW     | 0x0   | Interrupt Enable Field (nSTATUS Pin)  
 *  [10]    | RW     | 0x0   | Interrupt Enable Field (CONF_DONE Pin)
 *  [11]    | RW     | 0x0   | Interrupt Enable Field (FPGA_POWER_ON)
 *  [31:12] | ???    | 0x0   | *UNDEFINED*                           
 * 
 */
/*
 * Field : Interrupt Enable Field (nSTATUS) - ns
 * 
 * Enables interrupt generation for nSTATUS
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description      
 * :----------------------------|:------|:------------------
 *  ALT_MON_GPIO_INTEN_NS_E_DIS | 0x0   | Disable Interrupt
 *  ALT_MON_GPIO_INTEN_NS_E_EN  | 0x1   | Enable Interrupt 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_NS
 * 
 * Disable Interrupt
 */
#define ALT_MON_GPIO_INTEN_NS_E_DIS 0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_NS
 * 
 * Enable Interrupt
 */
#define ALT_MON_GPIO_INTEN_NS_E_EN  0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTEN_NS register field. */
#define ALT_MON_GPIO_INTEN_NS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTEN_NS register field. */
#define ALT_MON_GPIO_INTEN_NS_MSB        0
/* The width in bits of the ALT_MON_GPIO_INTEN_NS register field. */
#define ALT_MON_GPIO_INTEN_NS_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTEN_NS register field value. */
#define ALT_MON_GPIO_INTEN_NS_SET_MSK    0x00000001
/* The mask used to clear the ALT_MON_GPIO_INTEN_NS register field value. */
#define ALT_MON_GPIO_INTEN_NS_CLR_MSK    0xfffffffe
/* The reset value of the ALT_MON_GPIO_INTEN_NS register field. */
#define ALT_MON_GPIO_INTEN_NS_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTEN_NS field value from a register. */
#define ALT_MON_GPIO_INTEN_NS_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_MON_GPIO_INTEN_NS register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTEN_NS_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Interrupt Enable Field (CONF_DONE) - cd
 * 
 * Enables interrupt generation for CONF_DONE
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description      
 * :----------------------------|:------|:------------------
 *  ALT_MON_GPIO_INTEN_CD_E_DIS | 0x0   | Disable Interrupt
 *  ALT_MON_GPIO_INTEN_CD_E_EN  | 0x1   | Enable Interrupt 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_CD
 * 
 * Disable Interrupt
 */
#define ALT_MON_GPIO_INTEN_CD_E_DIS 0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_CD
 * 
 * Enable Interrupt
 */
#define ALT_MON_GPIO_INTEN_CD_E_EN  0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTEN_CD register field. */
#define ALT_MON_GPIO_INTEN_CD_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTEN_CD register field. */
#define ALT_MON_GPIO_INTEN_CD_MSB        1
/* The width in bits of the ALT_MON_GPIO_INTEN_CD register field. */
#define ALT_MON_GPIO_INTEN_CD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTEN_CD register field value. */
#define ALT_MON_GPIO_INTEN_CD_SET_MSK    0x00000002
/* The mask used to clear the ALT_MON_GPIO_INTEN_CD register field value. */
#define ALT_MON_GPIO_INTEN_CD_CLR_MSK    0xfffffffd
/* The reset value of the ALT_MON_GPIO_INTEN_CD register field. */
#define ALT_MON_GPIO_INTEN_CD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTEN_CD field value from a register. */
#define ALT_MON_GPIO_INTEN_CD_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_MON_GPIO_INTEN_CD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTEN_CD_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Interrupt Enable Field (INIT_DONE) - id
 * 
 * Enables interrupt generation for INIT_DONE
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description      
 * :----------------------------|:------|:------------------
 *  ALT_MON_GPIO_INTEN_ID_E_DIS | 0x0   | Disable Interrupt
 *  ALT_MON_GPIO_INTEN_ID_E_EN  | 0x1   | Enable Interrupt 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_ID
 * 
 * Disable Interrupt
 */
#define ALT_MON_GPIO_INTEN_ID_E_DIS 0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_ID
 * 
 * Enable Interrupt
 */
#define ALT_MON_GPIO_INTEN_ID_E_EN  0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTEN_ID register field. */
#define ALT_MON_GPIO_INTEN_ID_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTEN_ID register field. */
#define ALT_MON_GPIO_INTEN_ID_MSB        2
/* The width in bits of the ALT_MON_GPIO_INTEN_ID register field. */
#define ALT_MON_GPIO_INTEN_ID_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTEN_ID register field value. */
#define ALT_MON_GPIO_INTEN_ID_SET_MSK    0x00000004
/* The mask used to clear the ALT_MON_GPIO_INTEN_ID register field value. */
#define ALT_MON_GPIO_INTEN_ID_CLR_MSK    0xfffffffb
/* The reset value of the ALT_MON_GPIO_INTEN_ID register field. */
#define ALT_MON_GPIO_INTEN_ID_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTEN_ID field value from a register. */
#define ALT_MON_GPIO_INTEN_ID_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_MON_GPIO_INTEN_ID register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTEN_ID_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Interrupt Enable Field (CRC_ERROR) - crc
 * 
 * Enables interrupt generation for CRC_ERROR
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description      
 * :-----------------------------|:------|:------------------
 *  ALT_MON_GPIO_INTEN_CRC_E_DIS | 0x0   | Disable Interrupt
 *  ALT_MON_GPIO_INTEN_CRC_E_EN  | 0x1   | Enable Interrupt 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_CRC
 * 
 * Disable Interrupt
 */
#define ALT_MON_GPIO_INTEN_CRC_E_DIS    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_CRC
 * 
 * Enable Interrupt
 */
#define ALT_MON_GPIO_INTEN_CRC_E_EN     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTEN_CRC register field. */
#define ALT_MON_GPIO_INTEN_CRC_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTEN_CRC register field. */
#define ALT_MON_GPIO_INTEN_CRC_MSB        3
/* The width in bits of the ALT_MON_GPIO_INTEN_CRC register field. */
#define ALT_MON_GPIO_INTEN_CRC_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTEN_CRC register field value. */
#define ALT_MON_GPIO_INTEN_CRC_SET_MSK    0x00000008
/* The mask used to clear the ALT_MON_GPIO_INTEN_CRC register field value. */
#define ALT_MON_GPIO_INTEN_CRC_CLR_MSK    0xfffffff7
/* The reset value of the ALT_MON_GPIO_INTEN_CRC register field. */
#define ALT_MON_GPIO_INTEN_CRC_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTEN_CRC field value from a register. */
#define ALT_MON_GPIO_INTEN_CRC_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_MON_GPIO_INTEN_CRC register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTEN_CRC_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Interrupt Enable Field (CVP_CONF_DONE) - ccd
 * 
 * Enables interrupt generation for CVP_CONF_DONE
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description      
 * :-----------------------------|:------|:------------------
 *  ALT_MON_GPIO_INTEN_CCD_E_DIS | 0x0   | Disable Interrupt
 *  ALT_MON_GPIO_INTEN_CCD_E_EN  | 0x1   | Enable Interrupt 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_CCD
 * 
 * Disable Interrupt
 */
#define ALT_MON_GPIO_INTEN_CCD_E_DIS    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_CCD
 * 
 * Enable Interrupt
 */
#define ALT_MON_GPIO_INTEN_CCD_E_EN     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTEN_CCD register field. */
#define ALT_MON_GPIO_INTEN_CCD_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTEN_CCD register field. */
#define ALT_MON_GPIO_INTEN_CCD_MSB        4
/* The width in bits of the ALT_MON_GPIO_INTEN_CCD register field. */
#define ALT_MON_GPIO_INTEN_CCD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTEN_CCD register field value. */
#define ALT_MON_GPIO_INTEN_CCD_SET_MSK    0x00000010
/* The mask used to clear the ALT_MON_GPIO_INTEN_CCD register field value. */
#define ALT_MON_GPIO_INTEN_CCD_CLR_MSK    0xffffffef
/* The reset value of the ALT_MON_GPIO_INTEN_CCD register field. */
#define ALT_MON_GPIO_INTEN_CCD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTEN_CCD field value from a register. */
#define ALT_MON_GPIO_INTEN_CCD_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_MON_GPIO_INTEN_CCD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTEN_CCD_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Interrupt Enable Field (PR_READY) - prr
 * 
 * Enables interrupt generation for PR_READY
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description      
 * :-----------------------------|:------|:------------------
 *  ALT_MON_GPIO_INTEN_PRR_E_DIS | 0x0   | Disable Interrupt
 *  ALT_MON_GPIO_INTEN_PRR_E_EN  | 0x1   | Enable Interrupt 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_PRR
 * 
 * Disable Interrupt
 */
#define ALT_MON_GPIO_INTEN_PRR_E_DIS    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_PRR
 * 
 * Enable Interrupt
 */
#define ALT_MON_GPIO_INTEN_PRR_E_EN     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTEN_PRR register field. */
#define ALT_MON_GPIO_INTEN_PRR_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTEN_PRR register field. */
#define ALT_MON_GPIO_INTEN_PRR_MSB        5
/* The width in bits of the ALT_MON_GPIO_INTEN_PRR register field. */
#define ALT_MON_GPIO_INTEN_PRR_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTEN_PRR register field value. */
#define ALT_MON_GPIO_INTEN_PRR_SET_MSK    0x00000020
/* The mask used to clear the ALT_MON_GPIO_INTEN_PRR register field value. */
#define ALT_MON_GPIO_INTEN_PRR_CLR_MSK    0xffffffdf
/* The reset value of the ALT_MON_GPIO_INTEN_PRR register field. */
#define ALT_MON_GPIO_INTEN_PRR_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTEN_PRR field value from a register. */
#define ALT_MON_GPIO_INTEN_PRR_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_MON_GPIO_INTEN_PRR register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTEN_PRR_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Interrupt Enable Field (PR_ERROR) - pre
 * 
 * Enables interrupt generation for PR_ERROR
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description      
 * :-----------------------------|:------|:------------------
 *  ALT_MON_GPIO_INTEN_PRE_E_DIS | 0x0   | Disable Interrupt
 *  ALT_MON_GPIO_INTEN_PRE_E_EN  | 0x1   | Enable Interrupt 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_PRE
 * 
 * Disable Interrupt
 */
#define ALT_MON_GPIO_INTEN_PRE_E_DIS    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_PRE
 * 
 * Enable Interrupt
 */
#define ALT_MON_GPIO_INTEN_PRE_E_EN     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTEN_PRE register field. */
#define ALT_MON_GPIO_INTEN_PRE_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTEN_PRE register field. */
#define ALT_MON_GPIO_INTEN_PRE_MSB        6
/* The width in bits of the ALT_MON_GPIO_INTEN_PRE register field. */
#define ALT_MON_GPIO_INTEN_PRE_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTEN_PRE register field value. */
#define ALT_MON_GPIO_INTEN_PRE_SET_MSK    0x00000040
/* The mask used to clear the ALT_MON_GPIO_INTEN_PRE register field value. */
#define ALT_MON_GPIO_INTEN_PRE_CLR_MSK    0xffffffbf
/* The reset value of the ALT_MON_GPIO_INTEN_PRE register field. */
#define ALT_MON_GPIO_INTEN_PRE_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTEN_PRE field value from a register. */
#define ALT_MON_GPIO_INTEN_PRE_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_MON_GPIO_INTEN_PRE register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTEN_PRE_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Interrupt Enable Field (PR_DONE) - prd
 * 
 * Enables interrupt generation for PR_DONE
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description      
 * :-----------------------------|:------|:------------------
 *  ALT_MON_GPIO_INTEN_PRD_E_DIS | 0x0   | Disable Interrupt
 *  ALT_MON_GPIO_INTEN_PRD_E_EN  | 0x1   | Enable Interrupt 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_PRD
 * 
 * Disable Interrupt
 */
#define ALT_MON_GPIO_INTEN_PRD_E_DIS    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_PRD
 * 
 * Enable Interrupt
 */
#define ALT_MON_GPIO_INTEN_PRD_E_EN     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTEN_PRD register field. */
#define ALT_MON_GPIO_INTEN_PRD_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTEN_PRD register field. */
#define ALT_MON_GPIO_INTEN_PRD_MSB        7
/* The width in bits of the ALT_MON_GPIO_INTEN_PRD register field. */
#define ALT_MON_GPIO_INTEN_PRD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTEN_PRD register field value. */
#define ALT_MON_GPIO_INTEN_PRD_SET_MSK    0x00000080
/* The mask used to clear the ALT_MON_GPIO_INTEN_PRD register field value. */
#define ALT_MON_GPIO_INTEN_PRD_CLR_MSK    0xffffff7f
/* The reset value of the ALT_MON_GPIO_INTEN_PRD register field. */
#define ALT_MON_GPIO_INTEN_PRD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTEN_PRD field value from a register. */
#define ALT_MON_GPIO_INTEN_PRD_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_MON_GPIO_INTEN_PRD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTEN_PRD_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Interrupt Enable Field (nCONFIG Pin) - ncp
 * 
 * Enables interrupt generation for nCONFIG Pin
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description      
 * :-----------------------------|:------|:------------------
 *  ALT_MON_GPIO_INTEN_NCP_E_DIS | 0x0   | Disable Interrupt
 *  ALT_MON_GPIO_INTEN_NCP_E_EN  | 0x1   | Enable Interrupt 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_NCP
 * 
 * Disable Interrupt
 */
#define ALT_MON_GPIO_INTEN_NCP_E_DIS    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_NCP
 * 
 * Enable Interrupt
 */
#define ALT_MON_GPIO_INTEN_NCP_E_EN     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTEN_NCP register field. */
#define ALT_MON_GPIO_INTEN_NCP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTEN_NCP register field. */
#define ALT_MON_GPIO_INTEN_NCP_MSB        8
/* The width in bits of the ALT_MON_GPIO_INTEN_NCP register field. */
#define ALT_MON_GPIO_INTEN_NCP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTEN_NCP register field value. */
#define ALT_MON_GPIO_INTEN_NCP_SET_MSK    0x00000100
/* The mask used to clear the ALT_MON_GPIO_INTEN_NCP register field value. */
#define ALT_MON_GPIO_INTEN_NCP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_MON_GPIO_INTEN_NCP register field. */
#define ALT_MON_GPIO_INTEN_NCP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTEN_NCP field value from a register. */
#define ALT_MON_GPIO_INTEN_NCP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_MON_GPIO_INTEN_NCP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTEN_NCP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Interrupt Enable Field (nSTATUS Pin) - nsp
 * 
 * Enables interrupt generation for nSTATUS Pin
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description      
 * :-----------------------------|:------|:------------------
 *  ALT_MON_GPIO_INTEN_NSP_E_DIS | 0x0   | Disable Interrupt
 *  ALT_MON_GPIO_INTEN_NSP_E_EN  | 0x1   | Enable Interrupt 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_NSP
 * 
 * Disable Interrupt
 */
#define ALT_MON_GPIO_INTEN_NSP_E_DIS    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_NSP
 * 
 * Enable Interrupt
 */
#define ALT_MON_GPIO_INTEN_NSP_E_EN     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTEN_NSP register field. */
#define ALT_MON_GPIO_INTEN_NSP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTEN_NSP register field. */
#define ALT_MON_GPIO_INTEN_NSP_MSB        9
/* The width in bits of the ALT_MON_GPIO_INTEN_NSP register field. */
#define ALT_MON_GPIO_INTEN_NSP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTEN_NSP register field value. */
#define ALT_MON_GPIO_INTEN_NSP_SET_MSK    0x00000200
/* The mask used to clear the ALT_MON_GPIO_INTEN_NSP register field value. */
#define ALT_MON_GPIO_INTEN_NSP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_MON_GPIO_INTEN_NSP register field. */
#define ALT_MON_GPIO_INTEN_NSP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTEN_NSP field value from a register. */
#define ALT_MON_GPIO_INTEN_NSP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_MON_GPIO_INTEN_NSP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTEN_NSP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Interrupt Enable Field (CONF_DONE Pin) - cdp
 * 
 * Enables interrupt generation for CONF_DONE Pin
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description      
 * :-----------------------------|:------|:------------------
 *  ALT_MON_GPIO_INTEN_CDP_E_DIS | 0x0   | Disable Interrupt
 *  ALT_MON_GPIO_INTEN_CDP_E_EN  | 0x1   | Enable Interrupt 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_CDP
 * 
 * Disable Interrupt
 */
#define ALT_MON_GPIO_INTEN_CDP_E_DIS    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_CDP
 * 
 * Enable Interrupt
 */
#define ALT_MON_GPIO_INTEN_CDP_E_EN     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTEN_CDP register field. */
#define ALT_MON_GPIO_INTEN_CDP_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTEN_CDP register field. */
#define ALT_MON_GPIO_INTEN_CDP_MSB        10
/* The width in bits of the ALT_MON_GPIO_INTEN_CDP register field. */
#define ALT_MON_GPIO_INTEN_CDP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTEN_CDP register field value. */
#define ALT_MON_GPIO_INTEN_CDP_SET_MSK    0x00000400
/* The mask used to clear the ALT_MON_GPIO_INTEN_CDP register field value. */
#define ALT_MON_GPIO_INTEN_CDP_CLR_MSK    0xfffffbff
/* The reset value of the ALT_MON_GPIO_INTEN_CDP register field. */
#define ALT_MON_GPIO_INTEN_CDP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTEN_CDP field value from a register. */
#define ALT_MON_GPIO_INTEN_CDP_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_MON_GPIO_INTEN_CDP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTEN_CDP_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Interrupt Enable Field (FPGA_POWER_ON) - fpo
 * 
 * Enables interrupt generation for FPGA_POWER_ON
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description      
 * :-----------------------------|:------|:------------------
 *  ALT_MON_GPIO_INTEN_FPO_E_DIS | 0x0   | Disable Interrupt
 *  ALT_MON_GPIO_INTEN_FPO_E_EN  | 0x1   | Enable Interrupt 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_FPO
 * 
 * Disable Interrupt
 */
#define ALT_MON_GPIO_INTEN_FPO_E_DIS    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTEN_FPO
 * 
 * Enable Interrupt
 */
#define ALT_MON_GPIO_INTEN_FPO_E_EN     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTEN_FPO register field. */
#define ALT_MON_GPIO_INTEN_FPO_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTEN_FPO register field. */
#define ALT_MON_GPIO_INTEN_FPO_MSB        11
/* The width in bits of the ALT_MON_GPIO_INTEN_FPO register field. */
#define ALT_MON_GPIO_INTEN_FPO_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTEN_FPO register field value. */
#define ALT_MON_GPIO_INTEN_FPO_SET_MSK    0x00000800
/* The mask used to clear the ALT_MON_GPIO_INTEN_FPO register field value. */
#define ALT_MON_GPIO_INTEN_FPO_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_MON_GPIO_INTEN_FPO register field. */
#define ALT_MON_GPIO_INTEN_FPO_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTEN_FPO field value from a register. */
#define ALT_MON_GPIO_INTEN_FPO_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_MON_GPIO_INTEN_FPO register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTEN_FPO_SET(value) (((value) << 11) & 0x00000800)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_MON_GPIO_INTEN.
 */
struct ALT_MON_GPIO_INTEN_s
{
    uint32_t  ns  :  1;  /* Interrupt Enable Field (nSTATUS) */
    uint32_t  cd  :  1;  /* Interrupt Enable Field (CONF_DONE) */
    uint32_t  id  :  1;  /* Interrupt Enable Field (INIT_DONE) */
    uint32_t  crc :  1;  /* Interrupt Enable Field (CRC_ERROR) */
    uint32_t  ccd :  1;  /* Interrupt Enable Field (CVP_CONF_DONE) */
    uint32_t  prr :  1;  /* Interrupt Enable Field (PR_READY) */
    uint32_t  pre :  1;  /* Interrupt Enable Field (PR_ERROR) */
    uint32_t  prd :  1;  /* Interrupt Enable Field (PR_DONE) */
    uint32_t  ncp :  1;  /* Interrupt Enable Field (nCONFIG Pin) */
    uint32_t  nsp :  1;  /* Interrupt Enable Field (nSTATUS Pin) */
    uint32_t  cdp :  1;  /* Interrupt Enable Field (CONF_DONE Pin) */
    uint32_t  fpo :  1;  /* Interrupt Enable Field (FPGA_POWER_ON) */
    uint32_t      : 20;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_MON_GPIO_INTEN. */
typedef volatile struct ALT_MON_GPIO_INTEN_s  ALT_MON_GPIO_INTEN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_MON_GPIO_INTEN register from the beginning of the component. */
#define ALT_MON_GPIO_INTEN_OFST        0x30
/* The address of the ALT_MON_GPIO_INTEN register. */
#define ALT_MON_GPIO_INTEN_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_MON_GPIO_INTEN_OFST))

/*
 * Register : Interrupt Mask Register - gpio_intmask
 * 
 * This register has 12 individual interrupt masks for the MON. Controls whether an
 * interrupt on Port A can create an interrupt for the interrupt controller by not
 * masking it. By default, all interrupts bits are unmasked. Whenever a 1 is
 * written to a bit in this register, it masks the interrupt generation capability
 * for this signal; otherwise interrupts are allowed through. The unmasked status
 * can be read as well as the resultant status after masking.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                         
 * :--------|:-------|:------|:-------------------------------------
 *  [0]     | RW     | 0x0   | Interrupt Mask Field (nSTATUS)      
 *  [1]     | RW     | 0x0   | Interrupt Mask Field (CONF_DONE)    
 *  [2]     | RW     | 0x0   | Interrupt Mask Field (INIT_DONE)    
 *  [3]     | RW     | 0x0   | Interrupt Mask Field (CRC_ERROR)    
 *  [4]     | RW     | 0x0   | Interrupt Mask Field (CVP_CONF_DONE)
 *  [5]     | RW     | 0x0   | Interrupt Mask Field (PR_READY)     
 *  [6]     | RW     | 0x0   | Interrupt Mask Field (PR_ERROR)     
 *  [7]     | RW     | 0x0   | Interrupt Mask Field (PR_DONE)      
 *  [8]     | RW     | 0x0   | Interrupt Mask Field (nCONFIG Pin)  
 *  [9]     | RW     | 0x0   | Interrupt Mask Field (nSTATUS Pin)  
 *  [10]    | RW     | 0x0   | Interrupt Mask Field (CONF_DONE Pin)
 *  [11]    | RW     | 0x0   | Interrupt Mask Field (FPGA_POWER_ON)
 *  [31:12] | ???    | 0x0   | *UNDEFINED*                         
 * 
 */
/*
 * Field : Interrupt Mask Field (nSTATUS) - ns
 * 
 * Controls whether an interrupt for nSTATUS can generate an interrupt to the
 * interrupt controller by not masking it. The unmasked status can be read as well
 * as the resultant status after masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description     
 * :-----------------------------|:------|:-----------------
 *  ALT_MON_GPIO_INTMSK_NS_E_DIS | 0x0   | Unmask Interrupt
 *  ALT_MON_GPIO_INTMSK_NS_E_EN  | 0x1   | Mask Interrupt  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_NS
 * 
 * Unmask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_NS_E_DIS    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_NS
 * 
 * Mask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_NS_E_EN     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTMSK_NS register field. */
#define ALT_MON_GPIO_INTMSK_NS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTMSK_NS register field. */
#define ALT_MON_GPIO_INTMSK_NS_MSB        0
/* The width in bits of the ALT_MON_GPIO_INTMSK_NS register field. */
#define ALT_MON_GPIO_INTMSK_NS_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTMSK_NS register field value. */
#define ALT_MON_GPIO_INTMSK_NS_SET_MSK    0x00000001
/* The mask used to clear the ALT_MON_GPIO_INTMSK_NS register field value. */
#define ALT_MON_GPIO_INTMSK_NS_CLR_MSK    0xfffffffe
/* The reset value of the ALT_MON_GPIO_INTMSK_NS register field. */
#define ALT_MON_GPIO_INTMSK_NS_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTMSK_NS field value from a register. */
#define ALT_MON_GPIO_INTMSK_NS_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_MON_GPIO_INTMSK_NS register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTMSK_NS_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Interrupt Mask Field (CONF_DONE) - cd
 * 
 * Controls whether an interrupt for CONF_DONE can generate an interrupt to the
 * interrupt controller by not masking it. The unmasked status can be read as well
 * as the resultant status after masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description     
 * :-----------------------------|:------|:-----------------
 *  ALT_MON_GPIO_INTMSK_CD_E_DIS | 0x0   | Unmask Interrupt
 *  ALT_MON_GPIO_INTMSK_CD_E_EN  | 0x1   | Mask Interrupt  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_CD
 * 
 * Unmask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_CD_E_DIS    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_CD
 * 
 * Mask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_CD_E_EN     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTMSK_CD register field. */
#define ALT_MON_GPIO_INTMSK_CD_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTMSK_CD register field. */
#define ALT_MON_GPIO_INTMSK_CD_MSB        1
/* The width in bits of the ALT_MON_GPIO_INTMSK_CD register field. */
#define ALT_MON_GPIO_INTMSK_CD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTMSK_CD register field value. */
#define ALT_MON_GPIO_INTMSK_CD_SET_MSK    0x00000002
/* The mask used to clear the ALT_MON_GPIO_INTMSK_CD register field value. */
#define ALT_MON_GPIO_INTMSK_CD_CLR_MSK    0xfffffffd
/* The reset value of the ALT_MON_GPIO_INTMSK_CD register field. */
#define ALT_MON_GPIO_INTMSK_CD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTMSK_CD field value from a register. */
#define ALT_MON_GPIO_INTMSK_CD_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_MON_GPIO_INTMSK_CD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTMSK_CD_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Interrupt Mask Field (INIT_DONE) - id
 * 
 * Controls whether an interrupt for INIT_DONE can generate an interrupt to the
 * interrupt controller by not masking it. The unmasked status can be read as well
 * as the resultant status after masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description     
 * :-----------------------------|:------|:-----------------
 *  ALT_MON_GPIO_INTMSK_ID_E_DIS | 0x0   | Unmask Interrupt
 *  ALT_MON_GPIO_INTMSK_ID_E_EN  | 0x1   | Mask Interrupt  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_ID
 * 
 * Unmask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_ID_E_DIS    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_ID
 * 
 * Mask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_ID_E_EN     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTMSK_ID register field. */
#define ALT_MON_GPIO_INTMSK_ID_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTMSK_ID register field. */
#define ALT_MON_GPIO_INTMSK_ID_MSB        2
/* The width in bits of the ALT_MON_GPIO_INTMSK_ID register field. */
#define ALT_MON_GPIO_INTMSK_ID_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTMSK_ID register field value. */
#define ALT_MON_GPIO_INTMSK_ID_SET_MSK    0x00000004
/* The mask used to clear the ALT_MON_GPIO_INTMSK_ID register field value. */
#define ALT_MON_GPIO_INTMSK_ID_CLR_MSK    0xfffffffb
/* The reset value of the ALT_MON_GPIO_INTMSK_ID register field. */
#define ALT_MON_GPIO_INTMSK_ID_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTMSK_ID field value from a register. */
#define ALT_MON_GPIO_INTMSK_ID_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_MON_GPIO_INTMSK_ID register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTMSK_ID_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Interrupt Mask Field (CRC_ERROR) - crc
 * 
 * Controls whether an interrupt for CRC_ERROR can generate an interrupt to the
 * interrupt controller by not masking it. The unmasked status can be read as well
 * as the resultant status after masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description     
 * :------------------------------|:------|:-----------------
 *  ALT_MON_GPIO_INTMSK_CRC_E_DIS | 0x0   | Unmask Interrupt
 *  ALT_MON_GPIO_INTMSK_CRC_E_EN  | 0x1   | Mask Interrupt  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_CRC
 * 
 * Unmask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_CRC_E_DIS   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_CRC
 * 
 * Mask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_CRC_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTMSK_CRC register field. */
#define ALT_MON_GPIO_INTMSK_CRC_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTMSK_CRC register field. */
#define ALT_MON_GPIO_INTMSK_CRC_MSB        3
/* The width in bits of the ALT_MON_GPIO_INTMSK_CRC register field. */
#define ALT_MON_GPIO_INTMSK_CRC_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTMSK_CRC register field value. */
#define ALT_MON_GPIO_INTMSK_CRC_SET_MSK    0x00000008
/* The mask used to clear the ALT_MON_GPIO_INTMSK_CRC register field value. */
#define ALT_MON_GPIO_INTMSK_CRC_CLR_MSK    0xfffffff7
/* The reset value of the ALT_MON_GPIO_INTMSK_CRC register field. */
#define ALT_MON_GPIO_INTMSK_CRC_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTMSK_CRC field value from a register. */
#define ALT_MON_GPIO_INTMSK_CRC_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_MON_GPIO_INTMSK_CRC register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTMSK_CRC_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Interrupt Mask Field (CVP_CONF_DONE) - ccd
 * 
 * Controls whether an interrupt for CVP_CONF_DONE can generate an interrupt to the
 * interrupt controller by not masking it. The unmasked status can be read as well
 * as the resultant status after masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description     
 * :------------------------------|:------|:-----------------
 *  ALT_MON_GPIO_INTMSK_CCD_E_DIS | 0x0   | Unmask Interrupt
 *  ALT_MON_GPIO_INTMSK_CCD_E_EN  | 0x1   | Mask Interrupt  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_CCD
 * 
 * Unmask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_CCD_E_DIS   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_CCD
 * 
 * Mask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_CCD_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTMSK_CCD register field. */
#define ALT_MON_GPIO_INTMSK_CCD_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTMSK_CCD register field. */
#define ALT_MON_GPIO_INTMSK_CCD_MSB        4
/* The width in bits of the ALT_MON_GPIO_INTMSK_CCD register field. */
#define ALT_MON_GPIO_INTMSK_CCD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTMSK_CCD register field value. */
#define ALT_MON_GPIO_INTMSK_CCD_SET_MSK    0x00000010
/* The mask used to clear the ALT_MON_GPIO_INTMSK_CCD register field value. */
#define ALT_MON_GPIO_INTMSK_CCD_CLR_MSK    0xffffffef
/* The reset value of the ALT_MON_GPIO_INTMSK_CCD register field. */
#define ALT_MON_GPIO_INTMSK_CCD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTMSK_CCD field value from a register. */
#define ALT_MON_GPIO_INTMSK_CCD_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_MON_GPIO_INTMSK_CCD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTMSK_CCD_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Interrupt Mask Field (PR_READY) - prr
 * 
 * Controls whether an interrupt for PR_READY can generate an interrupt to the
 * interrupt controller by not masking it. The unmasked status can be read as well
 * as the resultant status after masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description     
 * :------------------------------|:------|:-----------------
 *  ALT_MON_GPIO_INTMSK_PRR_E_DIS | 0x0   | Unmask Interrupt
 *  ALT_MON_GPIO_INTMSK_PRR_E_EN  | 0x1   | Mask Interrupt  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_PRR
 * 
 * Unmask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_PRR_E_DIS   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_PRR
 * 
 * Mask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_PRR_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTMSK_PRR register field. */
#define ALT_MON_GPIO_INTMSK_PRR_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTMSK_PRR register field. */
#define ALT_MON_GPIO_INTMSK_PRR_MSB        5
/* The width in bits of the ALT_MON_GPIO_INTMSK_PRR register field. */
#define ALT_MON_GPIO_INTMSK_PRR_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTMSK_PRR register field value. */
#define ALT_MON_GPIO_INTMSK_PRR_SET_MSK    0x00000020
/* The mask used to clear the ALT_MON_GPIO_INTMSK_PRR register field value. */
#define ALT_MON_GPIO_INTMSK_PRR_CLR_MSK    0xffffffdf
/* The reset value of the ALT_MON_GPIO_INTMSK_PRR register field. */
#define ALT_MON_GPIO_INTMSK_PRR_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTMSK_PRR field value from a register. */
#define ALT_MON_GPIO_INTMSK_PRR_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_MON_GPIO_INTMSK_PRR register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTMSK_PRR_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Interrupt Mask Field (PR_ERROR) - pre
 * 
 * Controls whether an interrupt for PR_ERROR can generate an interrupt to the
 * interrupt controller by not masking it. The unmasked status can be read as well
 * as the resultant status after masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description     
 * :------------------------------|:------|:-----------------
 *  ALT_MON_GPIO_INTMSK_PRE_E_DIS | 0x0   | Unmask Interrupt
 *  ALT_MON_GPIO_INTMSK_PRE_E_EN  | 0x1   | Mask Interrupt  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_PRE
 * 
 * Unmask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_PRE_E_DIS   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_PRE
 * 
 * Mask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_PRE_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTMSK_PRE register field. */
#define ALT_MON_GPIO_INTMSK_PRE_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTMSK_PRE register field. */
#define ALT_MON_GPIO_INTMSK_PRE_MSB        6
/* The width in bits of the ALT_MON_GPIO_INTMSK_PRE register field. */
#define ALT_MON_GPIO_INTMSK_PRE_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTMSK_PRE register field value. */
#define ALT_MON_GPIO_INTMSK_PRE_SET_MSK    0x00000040
/* The mask used to clear the ALT_MON_GPIO_INTMSK_PRE register field value. */
#define ALT_MON_GPIO_INTMSK_PRE_CLR_MSK    0xffffffbf
/* The reset value of the ALT_MON_GPIO_INTMSK_PRE register field. */
#define ALT_MON_GPIO_INTMSK_PRE_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTMSK_PRE field value from a register. */
#define ALT_MON_GPIO_INTMSK_PRE_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_MON_GPIO_INTMSK_PRE register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTMSK_PRE_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Interrupt Mask Field (PR_DONE) - prd
 * 
 * Controls whether an interrupt for PR_DONE can generate an interrupt to the
 * interrupt controller by not masking it. The unmasked status can be read as well
 * as the resultant status after masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description     
 * :------------------------------|:------|:-----------------
 *  ALT_MON_GPIO_INTMSK_PRD_E_DIS | 0x0   | Unmask Interrupt
 *  ALT_MON_GPIO_INTMSK_PRD_E_EN  | 0x1   | Mask Interrupt  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_PRD
 * 
 * Unmask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_PRD_E_DIS   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_PRD
 * 
 * Mask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_PRD_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTMSK_PRD register field. */
#define ALT_MON_GPIO_INTMSK_PRD_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTMSK_PRD register field. */
#define ALT_MON_GPIO_INTMSK_PRD_MSB        7
/* The width in bits of the ALT_MON_GPIO_INTMSK_PRD register field. */
#define ALT_MON_GPIO_INTMSK_PRD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTMSK_PRD register field value. */
#define ALT_MON_GPIO_INTMSK_PRD_SET_MSK    0x00000080
/* The mask used to clear the ALT_MON_GPIO_INTMSK_PRD register field value. */
#define ALT_MON_GPIO_INTMSK_PRD_CLR_MSK    0xffffff7f
/* The reset value of the ALT_MON_GPIO_INTMSK_PRD register field. */
#define ALT_MON_GPIO_INTMSK_PRD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTMSK_PRD field value from a register. */
#define ALT_MON_GPIO_INTMSK_PRD_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_MON_GPIO_INTMSK_PRD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTMSK_PRD_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Interrupt Mask Field (nCONFIG Pin) - ncp
 * 
 * Controls whether an interrupt for nCONFIG Pin can generate an interrupt to the
 * interrupt controller by not masking it. The unmasked status can be read as well
 * as the resultant status after masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description     
 * :------------------------------|:------|:-----------------
 *  ALT_MON_GPIO_INTMSK_NCP_E_DIS | 0x0   | Unmask Interrupt
 *  ALT_MON_GPIO_INTMSK_NCP_E_EN  | 0x1   | Mask Interrupt  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_NCP
 * 
 * Unmask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_NCP_E_DIS   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_NCP
 * 
 * Mask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_NCP_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTMSK_NCP register field. */
#define ALT_MON_GPIO_INTMSK_NCP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTMSK_NCP register field. */
#define ALT_MON_GPIO_INTMSK_NCP_MSB        8
/* The width in bits of the ALT_MON_GPIO_INTMSK_NCP register field. */
#define ALT_MON_GPIO_INTMSK_NCP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTMSK_NCP register field value. */
#define ALT_MON_GPIO_INTMSK_NCP_SET_MSK    0x00000100
/* The mask used to clear the ALT_MON_GPIO_INTMSK_NCP register field value. */
#define ALT_MON_GPIO_INTMSK_NCP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_MON_GPIO_INTMSK_NCP register field. */
#define ALT_MON_GPIO_INTMSK_NCP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTMSK_NCP field value from a register. */
#define ALT_MON_GPIO_INTMSK_NCP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_MON_GPIO_INTMSK_NCP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTMSK_NCP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Interrupt Mask Field (nSTATUS Pin) - nsp
 * 
 * Controls whether an interrupt for nSTATUS Pin can generate an interrupt to the
 * interrupt controller by not masking it. The unmasked status can be read as well
 * as the resultant status after masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description     
 * :------------------------------|:------|:-----------------
 *  ALT_MON_GPIO_INTMSK_NSP_E_DIS | 0x0   | Unmask Interrupt
 *  ALT_MON_GPIO_INTMSK_NSP_E_EN  | 0x1   | Mask Interrupt  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_NSP
 * 
 * Unmask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_NSP_E_DIS   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_NSP
 * 
 * Mask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_NSP_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTMSK_NSP register field. */
#define ALT_MON_GPIO_INTMSK_NSP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTMSK_NSP register field. */
#define ALT_MON_GPIO_INTMSK_NSP_MSB        9
/* The width in bits of the ALT_MON_GPIO_INTMSK_NSP register field. */
#define ALT_MON_GPIO_INTMSK_NSP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTMSK_NSP register field value. */
#define ALT_MON_GPIO_INTMSK_NSP_SET_MSK    0x00000200
/* The mask used to clear the ALT_MON_GPIO_INTMSK_NSP register field value. */
#define ALT_MON_GPIO_INTMSK_NSP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_MON_GPIO_INTMSK_NSP register field. */
#define ALT_MON_GPIO_INTMSK_NSP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTMSK_NSP field value from a register. */
#define ALT_MON_GPIO_INTMSK_NSP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_MON_GPIO_INTMSK_NSP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTMSK_NSP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Interrupt Mask Field (CONF_DONE Pin) - cdp
 * 
 * Controls whether an interrupt for CONF_DONE Pin can generate an interrupt to the
 * interrupt controller by not masking it. The unmasked status can be read as well
 * as the resultant status after masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description     
 * :------------------------------|:------|:-----------------
 *  ALT_MON_GPIO_INTMSK_CDP_E_DIS | 0x0   | Unmask Interrupt
 *  ALT_MON_GPIO_INTMSK_CDP_E_EN  | 0x1   | Mask Interrupt  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_CDP
 * 
 * Unmask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_CDP_E_DIS   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_CDP
 * 
 * Mask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_CDP_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTMSK_CDP register field. */
#define ALT_MON_GPIO_INTMSK_CDP_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTMSK_CDP register field. */
#define ALT_MON_GPIO_INTMSK_CDP_MSB        10
/* The width in bits of the ALT_MON_GPIO_INTMSK_CDP register field. */
#define ALT_MON_GPIO_INTMSK_CDP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTMSK_CDP register field value. */
#define ALT_MON_GPIO_INTMSK_CDP_SET_MSK    0x00000400
/* The mask used to clear the ALT_MON_GPIO_INTMSK_CDP register field value. */
#define ALT_MON_GPIO_INTMSK_CDP_CLR_MSK    0xfffffbff
/* The reset value of the ALT_MON_GPIO_INTMSK_CDP register field. */
#define ALT_MON_GPIO_INTMSK_CDP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTMSK_CDP field value from a register. */
#define ALT_MON_GPIO_INTMSK_CDP_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_MON_GPIO_INTMSK_CDP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTMSK_CDP_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Interrupt Mask Field (FPGA_POWER_ON) - fpo
 * 
 * Controls whether an interrupt for FPGA_POWER_ON can generate an interrupt to the
 * interrupt controller by not masking it. The unmasked status can be read as well
 * as the resultant status after masking.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description     
 * :------------------------------|:------|:-----------------
 *  ALT_MON_GPIO_INTMSK_FPO_E_DIS | 0x0   | Unmask Interrupt
 *  ALT_MON_GPIO_INTMSK_FPO_E_EN  | 0x1   | Mask Interrupt  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_FPO
 * 
 * Unmask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_FPO_E_DIS   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTMSK_FPO
 * 
 * Mask Interrupt
 */
#define ALT_MON_GPIO_INTMSK_FPO_E_EN    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTMSK_FPO register field. */
#define ALT_MON_GPIO_INTMSK_FPO_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTMSK_FPO register field. */
#define ALT_MON_GPIO_INTMSK_FPO_MSB        11
/* The width in bits of the ALT_MON_GPIO_INTMSK_FPO register field. */
#define ALT_MON_GPIO_INTMSK_FPO_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTMSK_FPO register field value. */
#define ALT_MON_GPIO_INTMSK_FPO_SET_MSK    0x00000800
/* The mask used to clear the ALT_MON_GPIO_INTMSK_FPO register field value. */
#define ALT_MON_GPIO_INTMSK_FPO_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_MON_GPIO_INTMSK_FPO register field. */
#define ALT_MON_GPIO_INTMSK_FPO_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTMSK_FPO field value from a register. */
#define ALT_MON_GPIO_INTMSK_FPO_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_MON_GPIO_INTMSK_FPO register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTMSK_FPO_SET(value) (((value) << 11) & 0x00000800)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_MON_GPIO_INTMSK.
 */
struct ALT_MON_GPIO_INTMSK_s
{
    uint32_t  ns  :  1;  /* Interrupt Mask Field (nSTATUS) */
    uint32_t  cd  :  1;  /* Interrupt Mask Field (CONF_DONE) */
    uint32_t  id  :  1;  /* Interrupt Mask Field (INIT_DONE) */
    uint32_t  crc :  1;  /* Interrupt Mask Field (CRC_ERROR) */
    uint32_t  ccd :  1;  /* Interrupt Mask Field (CVP_CONF_DONE) */
    uint32_t  prr :  1;  /* Interrupt Mask Field (PR_READY) */
    uint32_t  pre :  1;  /* Interrupt Mask Field (PR_ERROR) */
    uint32_t  prd :  1;  /* Interrupt Mask Field (PR_DONE) */
    uint32_t  ncp :  1;  /* Interrupt Mask Field (nCONFIG Pin) */
    uint32_t  nsp :  1;  /* Interrupt Mask Field (nSTATUS Pin) */
    uint32_t  cdp :  1;  /* Interrupt Mask Field (CONF_DONE Pin) */
    uint32_t  fpo :  1;  /* Interrupt Mask Field (FPGA_POWER_ON) */
    uint32_t      : 20;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_MON_GPIO_INTMSK. */
typedef volatile struct ALT_MON_GPIO_INTMSK_s  ALT_MON_GPIO_INTMSK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_MON_GPIO_INTMSK register from the beginning of the component. */
#define ALT_MON_GPIO_INTMSK_OFST        0x34
/* The address of the ALT_MON_GPIO_INTMSK register. */
#define ALT_MON_GPIO_INTMSK_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_MON_GPIO_INTMSK_OFST))

/*
 * Register : Interrupt Level Register - gpio_inttype_level
 * 
 * The interrupt level register defines the type of interrupt (edge or level) for
 * each GPIO input.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                          
 * :--------|:-------|:------|:--------------------------------------
 *  [0]     | RW     | 0x0   | Interrupt Level Field (nSTATUS)      
 *  [1]     | RW     | 0x0   | Interrupt Level Field (CONF_DONE)    
 *  [2]     | RW     | 0x0   | Interrupt Level Field (INIT_DONE)    
 *  [3]     | RW     | 0x0   | Interrupt Level Field (CRC_ERROR)    
 *  [4]     | RW     | 0x0   | Interrupt Level Field (CVP_CONF_DONE)
 *  [5]     | RW     | 0x0   | Interrupt Level Field (PR_READY)     
 *  [6]     | RW     | 0x0   | Interrupt Level Field (PR_ERROR)     
 *  [7]     | RW     | 0x0   | Interrupt Level Field (PR_DONE)      
 *  [8]     | RW     | 0x0   | Interrupt Level Field (nCONFIG Pin)  
 *  [9]     | RW     | 0x0   | Interrupt Level Field (nSTATUS Pin)  
 *  [10]    | RW     | 0x0   | Interrupt Level Field (CONF_DONE Pin)
 *  [11]    | RW     | 0x0   | Interrupt Level Field (FPGA_POWER_ON)
 *  [31:12] | ???    | 0x0   | *UNDEFINED*                          
 * 
 */
/*
 * Field : Interrupt Level Field (nSTATUS) - ns
 * 
 * Controls whether the level of nSTATUS or an edge on nSTATUS generates an
 * interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description    
 * :--------------------------------------|:------|:----------------
 *  ALT_MON_GPIO_INTTYPE_LEVEL_NS_E_LEVEL | 0x0   | Level-sensitive
 *  ALT_MON_GPIO_INTTYPE_LEVEL_NS_E_EDGE  | 0x1   | Edge-sensitive 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_NS
 * 
 * Level-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NS_E_LEVEL   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_NS
 * 
 * Edge-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NS_E_EDGE    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_NS register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_NS register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NS_MSB        0
/* The width in bits of the ALT_MON_GPIO_INTTYPE_LEVEL_NS register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NS_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTTYPE_LEVEL_NS register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NS_SET_MSK    0x00000001
/* The mask used to clear the ALT_MON_GPIO_INTTYPE_LEVEL_NS register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NS_CLR_MSK    0xfffffffe
/* The reset value of the ALT_MON_GPIO_INTTYPE_LEVEL_NS register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NS_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTTYPE_LEVEL_NS field value from a register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NS_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_MON_GPIO_INTTYPE_LEVEL_NS register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NS_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Interrupt Level Field (CONF_DONE) - cd
 * 
 * Controls whether the level of CONF_DONE or an edge on CONF_DONE generates an
 * interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description    
 * :--------------------------------------|:------|:----------------
 *  ALT_MON_GPIO_INTTYPE_LEVEL_CD_E_LEVEL | 0x0   | Level-sensitive
 *  ALT_MON_GPIO_INTTYPE_LEVEL_CD_E_EDGE  | 0x1   | Edge-sensitive 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_CD
 * 
 * Level-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CD_E_LEVEL   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_CD
 * 
 * Edge-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CD_E_EDGE    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_CD register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CD_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_CD register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CD_MSB        1
/* The width in bits of the ALT_MON_GPIO_INTTYPE_LEVEL_CD register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTTYPE_LEVEL_CD register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CD_SET_MSK    0x00000002
/* The mask used to clear the ALT_MON_GPIO_INTTYPE_LEVEL_CD register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CD_CLR_MSK    0xfffffffd
/* The reset value of the ALT_MON_GPIO_INTTYPE_LEVEL_CD register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTTYPE_LEVEL_CD field value from a register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CD_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_MON_GPIO_INTTYPE_LEVEL_CD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CD_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Interrupt Level Field (INIT_DONE) - id
 * 
 * Controls whether the level of INIT_DONE or an edge on INIT_DONE generates an
 * interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description    
 * :--------------------------------------|:------|:----------------
 *  ALT_MON_GPIO_INTTYPE_LEVEL_ID_E_LEVEL | 0x0   | Level-sensitive
 *  ALT_MON_GPIO_INTTYPE_LEVEL_ID_E_EDGE  | 0x1   | Edge-sensitive 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_ID
 * 
 * Level-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_ID_E_LEVEL   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_ID
 * 
 * Edge-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_ID_E_EDGE    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_ID register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_ID_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_ID register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_ID_MSB        2
/* The width in bits of the ALT_MON_GPIO_INTTYPE_LEVEL_ID register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_ID_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTTYPE_LEVEL_ID register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_ID_SET_MSK    0x00000004
/* The mask used to clear the ALT_MON_GPIO_INTTYPE_LEVEL_ID register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_ID_CLR_MSK    0xfffffffb
/* The reset value of the ALT_MON_GPIO_INTTYPE_LEVEL_ID register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_ID_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTTYPE_LEVEL_ID field value from a register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_ID_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_MON_GPIO_INTTYPE_LEVEL_ID register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_ID_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Interrupt Level Field (CRC_ERROR) - crc
 * 
 * Controls whether the level of CRC_ERROR or an edge on CRC_ERROR generates an
 * interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description    
 * :---------------------------------------|:------|:----------------
 *  ALT_MON_GPIO_INTTYPE_LEVEL_CRC_E_LEVEL | 0x0   | Level-sensitive
 *  ALT_MON_GPIO_INTTYPE_LEVEL_CRC_E_EDGE  | 0x1   | Edge-sensitive 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_CRC
 * 
 * Level-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CRC_E_LEVEL  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_CRC
 * 
 * Edge-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CRC_E_EDGE   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_CRC register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CRC_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_CRC register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CRC_MSB        3
/* The width in bits of the ALT_MON_GPIO_INTTYPE_LEVEL_CRC register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CRC_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTTYPE_LEVEL_CRC register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CRC_SET_MSK    0x00000008
/* The mask used to clear the ALT_MON_GPIO_INTTYPE_LEVEL_CRC register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CRC_CLR_MSK    0xfffffff7
/* The reset value of the ALT_MON_GPIO_INTTYPE_LEVEL_CRC register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CRC_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTTYPE_LEVEL_CRC field value from a register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CRC_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_MON_GPIO_INTTYPE_LEVEL_CRC register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CRC_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Interrupt Level Field (CVP_CONF_DONE) - ccd
 * 
 * Controls whether the level of CVP_CONF_DONE or an edge on CVP_CONF_DONE
 * generates an interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description    
 * :---------------------------------------|:------|:----------------
 *  ALT_MON_GPIO_INTTYPE_LEVEL_CCD_E_LEVEL | 0x0   | Level-sensitive
 *  ALT_MON_GPIO_INTTYPE_LEVEL_CCD_E_EDGE  | 0x1   | Edge-sensitive 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_CCD
 * 
 * Level-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CCD_E_LEVEL  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_CCD
 * 
 * Edge-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CCD_E_EDGE   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_CCD register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CCD_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_CCD register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CCD_MSB        4
/* The width in bits of the ALT_MON_GPIO_INTTYPE_LEVEL_CCD register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CCD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTTYPE_LEVEL_CCD register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CCD_SET_MSK    0x00000010
/* The mask used to clear the ALT_MON_GPIO_INTTYPE_LEVEL_CCD register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CCD_CLR_MSK    0xffffffef
/* The reset value of the ALT_MON_GPIO_INTTYPE_LEVEL_CCD register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CCD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTTYPE_LEVEL_CCD field value from a register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CCD_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_MON_GPIO_INTTYPE_LEVEL_CCD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CCD_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Interrupt Level Field (PR_READY) - prr
 * 
 * Controls whether the level of PR_READY or an edge on PR_READY generates an
 * interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description    
 * :---------------------------------------|:------|:----------------
 *  ALT_MON_GPIO_INTTYPE_LEVEL_PRR_E_LEVEL | 0x0   | Level-sensitive
 *  ALT_MON_GPIO_INTTYPE_LEVEL_PRR_E_EDGE  | 0x1   | Edge-sensitive 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_PRR
 * 
 * Level-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRR_E_LEVEL  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_PRR
 * 
 * Edge-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRR_E_EDGE   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_PRR register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRR_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_PRR register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRR_MSB        5
/* The width in bits of the ALT_MON_GPIO_INTTYPE_LEVEL_PRR register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRR_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTTYPE_LEVEL_PRR register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRR_SET_MSK    0x00000020
/* The mask used to clear the ALT_MON_GPIO_INTTYPE_LEVEL_PRR register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRR_CLR_MSK    0xffffffdf
/* The reset value of the ALT_MON_GPIO_INTTYPE_LEVEL_PRR register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRR_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTTYPE_LEVEL_PRR field value from a register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRR_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_MON_GPIO_INTTYPE_LEVEL_PRR register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRR_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Interrupt Level Field (PR_ERROR) - pre
 * 
 * Controls whether the level of PR_ERROR or an edge on PR_ERROR generates an
 * interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description    
 * :---------------------------------------|:------|:----------------
 *  ALT_MON_GPIO_INTTYPE_LEVEL_PRE_E_LEVEL | 0x0   | Level-sensitive
 *  ALT_MON_GPIO_INTTYPE_LEVEL_PRE_E_EDGE  | 0x1   | Edge-sensitive 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_PRE
 * 
 * Level-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRE_E_LEVEL  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_PRE
 * 
 * Edge-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRE_E_EDGE   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_PRE register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRE_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_PRE register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRE_MSB        6
/* The width in bits of the ALT_MON_GPIO_INTTYPE_LEVEL_PRE register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRE_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTTYPE_LEVEL_PRE register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRE_SET_MSK    0x00000040
/* The mask used to clear the ALT_MON_GPIO_INTTYPE_LEVEL_PRE register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRE_CLR_MSK    0xffffffbf
/* The reset value of the ALT_MON_GPIO_INTTYPE_LEVEL_PRE register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRE_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTTYPE_LEVEL_PRE field value from a register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRE_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_MON_GPIO_INTTYPE_LEVEL_PRE register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRE_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Interrupt Level Field (PR_DONE) - prd
 * 
 * Controls whether the level of PR_DONE or an edge on PR_DONE generates an
 * interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description    
 * :---------------------------------------|:------|:----------------
 *  ALT_MON_GPIO_INTTYPE_LEVEL_PRD_E_LEVEL | 0x0   | Level-sensitive
 *  ALT_MON_GPIO_INTTYPE_LEVEL_PRD_E_EDGE  | 0x1   | Edge-sensitive 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_PRD
 * 
 * Level-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRD_E_LEVEL  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_PRD
 * 
 * Edge-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRD_E_EDGE   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_PRD register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRD_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_PRD register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRD_MSB        7
/* The width in bits of the ALT_MON_GPIO_INTTYPE_LEVEL_PRD register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTTYPE_LEVEL_PRD register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRD_SET_MSK    0x00000080
/* The mask used to clear the ALT_MON_GPIO_INTTYPE_LEVEL_PRD register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRD_CLR_MSK    0xffffff7f
/* The reset value of the ALT_MON_GPIO_INTTYPE_LEVEL_PRD register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTTYPE_LEVEL_PRD field value from a register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRD_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_MON_GPIO_INTTYPE_LEVEL_PRD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_PRD_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Interrupt Level Field (nCONFIG Pin) - ncp
 * 
 * Controls whether the level of nCONFIG Pin or an edge on nCONFIG Pin generates an
 * interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description    
 * :---------------------------------------|:------|:----------------
 *  ALT_MON_GPIO_INTTYPE_LEVEL_NCP_E_LEVEL | 0x0   | Level-sensitive
 *  ALT_MON_GPIO_INTTYPE_LEVEL_NCP_E_EDGE  | 0x1   | Edge-sensitive 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_NCP
 * 
 * Level-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NCP_E_LEVEL  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_NCP
 * 
 * Edge-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NCP_E_EDGE   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_NCP register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NCP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_NCP register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NCP_MSB        8
/* The width in bits of the ALT_MON_GPIO_INTTYPE_LEVEL_NCP register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NCP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTTYPE_LEVEL_NCP register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NCP_SET_MSK    0x00000100
/* The mask used to clear the ALT_MON_GPIO_INTTYPE_LEVEL_NCP register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NCP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_MON_GPIO_INTTYPE_LEVEL_NCP register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NCP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTTYPE_LEVEL_NCP field value from a register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NCP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_MON_GPIO_INTTYPE_LEVEL_NCP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NCP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Interrupt Level Field (nSTATUS Pin) - nsp
 * 
 * Controls whether the level of nSTATUS Pin or an edge on nSTATUS Pin generates an
 * interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description    
 * :---------------------------------------|:------|:----------------
 *  ALT_MON_GPIO_INTTYPE_LEVEL_NSP_E_LEVEL | 0x0   | Level-sensitive
 *  ALT_MON_GPIO_INTTYPE_LEVEL_NSP_E_EDGE  | 0x1   | Edge-sensitive 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_NSP
 * 
 * Level-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NSP_E_LEVEL  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_NSP
 * 
 * Edge-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NSP_E_EDGE   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_NSP register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NSP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_NSP register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NSP_MSB        9
/* The width in bits of the ALT_MON_GPIO_INTTYPE_LEVEL_NSP register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NSP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTTYPE_LEVEL_NSP register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NSP_SET_MSK    0x00000200
/* The mask used to clear the ALT_MON_GPIO_INTTYPE_LEVEL_NSP register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NSP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_MON_GPIO_INTTYPE_LEVEL_NSP register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NSP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTTYPE_LEVEL_NSP field value from a register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NSP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_MON_GPIO_INTTYPE_LEVEL_NSP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_NSP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Interrupt Level Field (CONF_DONE Pin) - cdp
 * 
 * Controls whether the level of CONF_DONE Pin or an edge on CONF_DONE Pin
 * generates an interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description    
 * :---------------------------------------|:------|:----------------
 *  ALT_MON_GPIO_INTTYPE_LEVEL_CDP_E_LEVEL | 0x0   | Level-sensitive
 *  ALT_MON_GPIO_INTTYPE_LEVEL_CDP_E_EDGE  | 0x1   | Edge-sensitive 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_CDP
 * 
 * Level-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CDP_E_LEVEL  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_CDP
 * 
 * Edge-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CDP_E_EDGE   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_CDP register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CDP_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_CDP register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CDP_MSB        10
/* The width in bits of the ALT_MON_GPIO_INTTYPE_LEVEL_CDP register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CDP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTTYPE_LEVEL_CDP register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CDP_SET_MSK    0x00000400
/* The mask used to clear the ALT_MON_GPIO_INTTYPE_LEVEL_CDP register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CDP_CLR_MSK    0xfffffbff
/* The reset value of the ALT_MON_GPIO_INTTYPE_LEVEL_CDP register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CDP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTTYPE_LEVEL_CDP field value from a register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CDP_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_MON_GPIO_INTTYPE_LEVEL_CDP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_CDP_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Interrupt Level Field (FPGA_POWER_ON) - fpo
 * 
 * Controls whether the level of FPGA_POWER_ON or an edge on FPGA_POWER_ON
 * generates an interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description    
 * :---------------------------------------|:------|:----------------
 *  ALT_MON_GPIO_INTTYPE_LEVEL_FPO_E_LEVEL | 0x0   | Level-sensitive
 *  ALT_MON_GPIO_INTTYPE_LEVEL_FPO_E_EDGE  | 0x1   | Edge-sensitive 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_FPO
 * 
 * Level-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_FPO_E_LEVEL  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTTYPE_LEVEL_FPO
 * 
 * Edge-sensitive
 */
#define ALT_MON_GPIO_INTTYPE_LEVEL_FPO_E_EDGE   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_FPO register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_FPO_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTTYPE_LEVEL_FPO register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_FPO_MSB        11
/* The width in bits of the ALT_MON_GPIO_INTTYPE_LEVEL_FPO register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_FPO_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTTYPE_LEVEL_FPO register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_FPO_SET_MSK    0x00000800
/* The mask used to clear the ALT_MON_GPIO_INTTYPE_LEVEL_FPO register field value. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_FPO_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_MON_GPIO_INTTYPE_LEVEL_FPO register field. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_FPO_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTTYPE_LEVEL_FPO field value from a register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_FPO_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_MON_GPIO_INTTYPE_LEVEL_FPO register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_FPO_SET(value) (((value) << 11) & 0x00000800)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_MON_GPIO_INTTYPE_LEVEL.
 */
struct ALT_MON_GPIO_INTTYPE_LEVEL_s
{
    uint32_t  ns  :  1;  /* Interrupt Level Field (nSTATUS) */
    uint32_t  cd  :  1;  /* Interrupt Level Field (CONF_DONE) */
    uint32_t  id  :  1;  /* Interrupt Level Field (INIT_DONE) */
    uint32_t  crc :  1;  /* Interrupt Level Field (CRC_ERROR) */
    uint32_t  ccd :  1;  /* Interrupt Level Field (CVP_CONF_DONE) */
    uint32_t  prr :  1;  /* Interrupt Level Field (PR_READY) */
    uint32_t  pre :  1;  /* Interrupt Level Field (PR_ERROR) */
    uint32_t  prd :  1;  /* Interrupt Level Field (PR_DONE) */
    uint32_t  ncp :  1;  /* Interrupt Level Field (nCONFIG Pin) */
    uint32_t  nsp :  1;  /* Interrupt Level Field (nSTATUS Pin) */
    uint32_t  cdp :  1;  /* Interrupt Level Field (CONF_DONE Pin) */
    uint32_t  fpo :  1;  /* Interrupt Level Field (FPGA_POWER_ON) */
    uint32_t      : 20;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_MON_GPIO_INTTYPE_LEVEL. */
typedef volatile struct ALT_MON_GPIO_INTTYPE_LEVEL_s  ALT_MON_GPIO_INTTYPE_LEVEL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_MON_GPIO_INTTYPE_LEVEL register from the beginning of the component. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_OFST        0x38
/* The address of the ALT_MON_GPIO_INTTYPE_LEVEL register. */
#define ALT_MON_GPIO_INTTYPE_LEVEL_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_MON_GPIO_INTTYPE_LEVEL_OFST))

/*
 * Register : Interrupt Polarity Register - gpio_int_polarity
 * 
 * Controls the polarity of interrupts that can occur on each GPIO input.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                           
 * :--------|:-------|:------|:---------------------------------------
 *  [0]     | RW     | 0x0   | Polarity Control Field (nSTATUS)      
 *  [1]     | RW     | 0x0   | Polarity Control Field (CONF_DONE)    
 *  [2]     | RW     | 0x0   | Polarity Control Field (INIT_DONE)    
 *  [3]     | RW     | 0x0   | Polarity Control Field (CRC_ERROR)    
 *  [4]     | RW     | 0x0   | Polarity Control Field (CVP_CONF_DONE)
 *  [5]     | RW     | 0x0   | Polarity Control Field (PR_READY)     
 *  [6]     | RW     | 0x0   | Polarity Control Field (PR_ERROR)     
 *  [7]     | RW     | 0x0   | Polarity Control Field (PR_DONE)      
 *  [8]     | RW     | 0x0   | Polarity Control Field (nCONFIG Pin)  
 *  [9]     | RW     | 0x0   | Polarity Control Field (nSTATUS Pin)  
 *  [10]    | RW     | 0x0   | Polarity Control Field (CONF_DONE Pin)
 *  [11]    | RW     | 0x0   | Polarity Control Field (FPGA_POWER_ON)
 *  [31:12] | ???    | 0x0   | *UNDEFINED*                           
 * 
 */
/*
 * Field : Polarity Control Field (nSTATUS) - ns
 * 
 * Controls the polarity of edge or level sensitivity for nSTATUS
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description
 * :----------------------------------|:------|:------------
 *  ALT_MON_GPIO_INT_POL_NS_E_ACTLOW  | 0x0   | Active low 
 *  ALT_MON_GPIO_INT_POL_NS_E_ACTHIGH | 0x1   | Active high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_NS
 * 
 * Active low
 */
#define ALT_MON_GPIO_INT_POL_NS_E_ACTLOW    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_NS
 * 
 * Active high
 */
#define ALT_MON_GPIO_INT_POL_NS_E_ACTHIGH   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INT_POL_NS register field. */
#define ALT_MON_GPIO_INT_POL_NS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INT_POL_NS register field. */
#define ALT_MON_GPIO_INT_POL_NS_MSB        0
/* The width in bits of the ALT_MON_GPIO_INT_POL_NS register field. */
#define ALT_MON_GPIO_INT_POL_NS_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INT_POL_NS register field value. */
#define ALT_MON_GPIO_INT_POL_NS_SET_MSK    0x00000001
/* The mask used to clear the ALT_MON_GPIO_INT_POL_NS register field value. */
#define ALT_MON_GPIO_INT_POL_NS_CLR_MSK    0xfffffffe
/* The reset value of the ALT_MON_GPIO_INT_POL_NS register field. */
#define ALT_MON_GPIO_INT_POL_NS_RESET      0x0
/* Extracts the ALT_MON_GPIO_INT_POL_NS field value from a register. */
#define ALT_MON_GPIO_INT_POL_NS_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_MON_GPIO_INT_POL_NS register field value suitable for setting the register. */
#define ALT_MON_GPIO_INT_POL_NS_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Polarity Control Field (CONF_DONE) - cd
 * 
 * Controls the polarity of edge or level sensitivity for CONF_DONE
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description
 * :----------------------------------|:------|:------------
 *  ALT_MON_GPIO_INT_POL_CD_E_ACTLOW  | 0x0   | Active low 
 *  ALT_MON_GPIO_INT_POL_CD_E_ACTHIGH | 0x1   | Active high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_CD
 * 
 * Active low
 */
#define ALT_MON_GPIO_INT_POL_CD_E_ACTLOW    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_CD
 * 
 * Active high
 */
#define ALT_MON_GPIO_INT_POL_CD_E_ACTHIGH   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INT_POL_CD register field. */
#define ALT_MON_GPIO_INT_POL_CD_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INT_POL_CD register field. */
#define ALT_MON_GPIO_INT_POL_CD_MSB        1
/* The width in bits of the ALT_MON_GPIO_INT_POL_CD register field. */
#define ALT_MON_GPIO_INT_POL_CD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INT_POL_CD register field value. */
#define ALT_MON_GPIO_INT_POL_CD_SET_MSK    0x00000002
/* The mask used to clear the ALT_MON_GPIO_INT_POL_CD register field value. */
#define ALT_MON_GPIO_INT_POL_CD_CLR_MSK    0xfffffffd
/* The reset value of the ALT_MON_GPIO_INT_POL_CD register field. */
#define ALT_MON_GPIO_INT_POL_CD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INT_POL_CD field value from a register. */
#define ALT_MON_GPIO_INT_POL_CD_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_MON_GPIO_INT_POL_CD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INT_POL_CD_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Polarity Control Field (INIT_DONE) - id
 * 
 * Controls the polarity of edge or level sensitivity for INIT_DONE
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description
 * :----------------------------------|:------|:------------
 *  ALT_MON_GPIO_INT_POL_ID_E_ACTLOW  | 0x0   | Active low 
 *  ALT_MON_GPIO_INT_POL_ID_E_ACTHIGH | 0x1   | Active high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_ID
 * 
 * Active low
 */
#define ALT_MON_GPIO_INT_POL_ID_E_ACTLOW    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_ID
 * 
 * Active high
 */
#define ALT_MON_GPIO_INT_POL_ID_E_ACTHIGH   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INT_POL_ID register field. */
#define ALT_MON_GPIO_INT_POL_ID_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INT_POL_ID register field. */
#define ALT_MON_GPIO_INT_POL_ID_MSB        2
/* The width in bits of the ALT_MON_GPIO_INT_POL_ID register field. */
#define ALT_MON_GPIO_INT_POL_ID_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INT_POL_ID register field value. */
#define ALT_MON_GPIO_INT_POL_ID_SET_MSK    0x00000004
/* The mask used to clear the ALT_MON_GPIO_INT_POL_ID register field value. */
#define ALT_MON_GPIO_INT_POL_ID_CLR_MSK    0xfffffffb
/* The reset value of the ALT_MON_GPIO_INT_POL_ID register field. */
#define ALT_MON_GPIO_INT_POL_ID_RESET      0x0
/* Extracts the ALT_MON_GPIO_INT_POL_ID field value from a register. */
#define ALT_MON_GPIO_INT_POL_ID_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_MON_GPIO_INT_POL_ID register field value suitable for setting the register. */
#define ALT_MON_GPIO_INT_POL_ID_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Polarity Control Field (CRC_ERROR) - crc
 * 
 * Controls the polarity of edge or level sensitivity for CRC_ERROR
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description
 * :-----------------------------------|:------|:------------
 *  ALT_MON_GPIO_INT_POL_CRC_E_ACTLOW  | 0x0   | Active low 
 *  ALT_MON_GPIO_INT_POL_CRC_E_ACTHIGH | 0x1   | Active high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_CRC
 * 
 * Active low
 */
#define ALT_MON_GPIO_INT_POL_CRC_E_ACTLOW   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_CRC
 * 
 * Active high
 */
#define ALT_MON_GPIO_INT_POL_CRC_E_ACTHIGH  0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INT_POL_CRC register field. */
#define ALT_MON_GPIO_INT_POL_CRC_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INT_POL_CRC register field. */
#define ALT_MON_GPIO_INT_POL_CRC_MSB        3
/* The width in bits of the ALT_MON_GPIO_INT_POL_CRC register field. */
#define ALT_MON_GPIO_INT_POL_CRC_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INT_POL_CRC register field value. */
#define ALT_MON_GPIO_INT_POL_CRC_SET_MSK    0x00000008
/* The mask used to clear the ALT_MON_GPIO_INT_POL_CRC register field value. */
#define ALT_MON_GPIO_INT_POL_CRC_CLR_MSK    0xfffffff7
/* The reset value of the ALT_MON_GPIO_INT_POL_CRC register field. */
#define ALT_MON_GPIO_INT_POL_CRC_RESET      0x0
/* Extracts the ALT_MON_GPIO_INT_POL_CRC field value from a register. */
#define ALT_MON_GPIO_INT_POL_CRC_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_MON_GPIO_INT_POL_CRC register field value suitable for setting the register. */
#define ALT_MON_GPIO_INT_POL_CRC_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Polarity Control Field (CVP_CONF_DONE) - ccd
 * 
 * Controls the polarity of edge or level sensitivity for CVP_CONF_DONE
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description
 * :-----------------------------------|:------|:------------
 *  ALT_MON_GPIO_INT_POL_CCD_E_ACTLOW  | 0x0   | Active low 
 *  ALT_MON_GPIO_INT_POL_CCD_E_ACTHIGH | 0x1   | Active high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_CCD
 * 
 * Active low
 */
#define ALT_MON_GPIO_INT_POL_CCD_E_ACTLOW   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_CCD
 * 
 * Active high
 */
#define ALT_MON_GPIO_INT_POL_CCD_E_ACTHIGH  0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INT_POL_CCD register field. */
#define ALT_MON_GPIO_INT_POL_CCD_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INT_POL_CCD register field. */
#define ALT_MON_GPIO_INT_POL_CCD_MSB        4
/* The width in bits of the ALT_MON_GPIO_INT_POL_CCD register field. */
#define ALT_MON_GPIO_INT_POL_CCD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INT_POL_CCD register field value. */
#define ALT_MON_GPIO_INT_POL_CCD_SET_MSK    0x00000010
/* The mask used to clear the ALT_MON_GPIO_INT_POL_CCD register field value. */
#define ALT_MON_GPIO_INT_POL_CCD_CLR_MSK    0xffffffef
/* The reset value of the ALT_MON_GPIO_INT_POL_CCD register field. */
#define ALT_MON_GPIO_INT_POL_CCD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INT_POL_CCD field value from a register. */
#define ALT_MON_GPIO_INT_POL_CCD_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_MON_GPIO_INT_POL_CCD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INT_POL_CCD_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Polarity Control Field (PR_READY) - prr
 * 
 * Controls the polarity of edge or level sensitivity for PR_READY
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description
 * :-----------------------------------|:------|:------------
 *  ALT_MON_GPIO_INT_POL_PRR_E_ACTLOW  | 0x0   | Active low 
 *  ALT_MON_GPIO_INT_POL_PRR_E_ACTHIGH | 0x1   | Active high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_PRR
 * 
 * Active low
 */
#define ALT_MON_GPIO_INT_POL_PRR_E_ACTLOW   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_PRR
 * 
 * Active high
 */
#define ALT_MON_GPIO_INT_POL_PRR_E_ACTHIGH  0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INT_POL_PRR register field. */
#define ALT_MON_GPIO_INT_POL_PRR_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INT_POL_PRR register field. */
#define ALT_MON_GPIO_INT_POL_PRR_MSB        5
/* The width in bits of the ALT_MON_GPIO_INT_POL_PRR register field. */
#define ALT_MON_GPIO_INT_POL_PRR_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INT_POL_PRR register field value. */
#define ALT_MON_GPIO_INT_POL_PRR_SET_MSK    0x00000020
/* The mask used to clear the ALT_MON_GPIO_INT_POL_PRR register field value. */
#define ALT_MON_GPIO_INT_POL_PRR_CLR_MSK    0xffffffdf
/* The reset value of the ALT_MON_GPIO_INT_POL_PRR register field. */
#define ALT_MON_GPIO_INT_POL_PRR_RESET      0x0
/* Extracts the ALT_MON_GPIO_INT_POL_PRR field value from a register. */
#define ALT_MON_GPIO_INT_POL_PRR_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_MON_GPIO_INT_POL_PRR register field value suitable for setting the register. */
#define ALT_MON_GPIO_INT_POL_PRR_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Polarity Control Field (PR_ERROR) - pre
 * 
 * Controls the polarity of edge or level sensitivity for PR_ERROR
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description
 * :-----------------------------------|:------|:------------
 *  ALT_MON_GPIO_INT_POL_PRE_E_ACTLOW  | 0x0   | Active low 
 *  ALT_MON_GPIO_INT_POL_PRE_E_ACTHIGH | 0x1   | Active high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_PRE
 * 
 * Active low
 */
#define ALT_MON_GPIO_INT_POL_PRE_E_ACTLOW   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_PRE
 * 
 * Active high
 */
#define ALT_MON_GPIO_INT_POL_PRE_E_ACTHIGH  0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INT_POL_PRE register field. */
#define ALT_MON_GPIO_INT_POL_PRE_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INT_POL_PRE register field. */
#define ALT_MON_GPIO_INT_POL_PRE_MSB        6
/* The width in bits of the ALT_MON_GPIO_INT_POL_PRE register field. */
#define ALT_MON_GPIO_INT_POL_PRE_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INT_POL_PRE register field value. */
#define ALT_MON_GPIO_INT_POL_PRE_SET_MSK    0x00000040
/* The mask used to clear the ALT_MON_GPIO_INT_POL_PRE register field value. */
#define ALT_MON_GPIO_INT_POL_PRE_CLR_MSK    0xffffffbf
/* The reset value of the ALT_MON_GPIO_INT_POL_PRE register field. */
#define ALT_MON_GPIO_INT_POL_PRE_RESET      0x0
/* Extracts the ALT_MON_GPIO_INT_POL_PRE field value from a register. */
#define ALT_MON_GPIO_INT_POL_PRE_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_MON_GPIO_INT_POL_PRE register field value suitable for setting the register. */
#define ALT_MON_GPIO_INT_POL_PRE_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Polarity Control Field (PR_DONE) - prd
 * 
 * Controls the polarity of edge or level sensitivity for PR_DONE
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description
 * :-----------------------------------|:------|:------------
 *  ALT_MON_GPIO_INT_POL_PRD_E_ACTLOW  | 0x0   | Active low 
 *  ALT_MON_GPIO_INT_POL_PRD_E_ACTHIGH | 0x1   | Active high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_PRD
 * 
 * Active low
 */
#define ALT_MON_GPIO_INT_POL_PRD_E_ACTLOW   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_PRD
 * 
 * Active high
 */
#define ALT_MON_GPIO_INT_POL_PRD_E_ACTHIGH  0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INT_POL_PRD register field. */
#define ALT_MON_GPIO_INT_POL_PRD_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INT_POL_PRD register field. */
#define ALT_MON_GPIO_INT_POL_PRD_MSB        7
/* The width in bits of the ALT_MON_GPIO_INT_POL_PRD register field. */
#define ALT_MON_GPIO_INT_POL_PRD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INT_POL_PRD register field value. */
#define ALT_MON_GPIO_INT_POL_PRD_SET_MSK    0x00000080
/* The mask used to clear the ALT_MON_GPIO_INT_POL_PRD register field value. */
#define ALT_MON_GPIO_INT_POL_PRD_CLR_MSK    0xffffff7f
/* The reset value of the ALT_MON_GPIO_INT_POL_PRD register field. */
#define ALT_MON_GPIO_INT_POL_PRD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INT_POL_PRD field value from a register. */
#define ALT_MON_GPIO_INT_POL_PRD_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_MON_GPIO_INT_POL_PRD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INT_POL_PRD_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Polarity Control Field (nCONFIG Pin) - ncp
 * 
 * Controls the polarity of edge or level sensitivity for nCONFIG Pin
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description
 * :-----------------------------------|:------|:------------
 *  ALT_MON_GPIO_INT_POL_NCP_E_ACTLOW  | 0x0   | Active low 
 *  ALT_MON_GPIO_INT_POL_NCP_E_ACTHIGH | 0x1   | Active high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_NCP
 * 
 * Active low
 */
#define ALT_MON_GPIO_INT_POL_NCP_E_ACTLOW   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_NCP
 * 
 * Active high
 */
#define ALT_MON_GPIO_INT_POL_NCP_E_ACTHIGH  0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INT_POL_NCP register field. */
#define ALT_MON_GPIO_INT_POL_NCP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INT_POL_NCP register field. */
#define ALT_MON_GPIO_INT_POL_NCP_MSB        8
/* The width in bits of the ALT_MON_GPIO_INT_POL_NCP register field. */
#define ALT_MON_GPIO_INT_POL_NCP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INT_POL_NCP register field value. */
#define ALT_MON_GPIO_INT_POL_NCP_SET_MSK    0x00000100
/* The mask used to clear the ALT_MON_GPIO_INT_POL_NCP register field value. */
#define ALT_MON_GPIO_INT_POL_NCP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_MON_GPIO_INT_POL_NCP register field. */
#define ALT_MON_GPIO_INT_POL_NCP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INT_POL_NCP field value from a register. */
#define ALT_MON_GPIO_INT_POL_NCP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_MON_GPIO_INT_POL_NCP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INT_POL_NCP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Polarity Control Field (nSTATUS Pin) - nsp
 * 
 * Controls the polarity of edge or level sensitivity for nSTATUS Pin
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description
 * :-----------------------------------|:------|:------------
 *  ALT_MON_GPIO_INT_POL_NSP_E_ACTLOW  | 0x0   | Active low 
 *  ALT_MON_GPIO_INT_POL_NSP_E_ACTHIGH | 0x1   | Active high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_NSP
 * 
 * Active low
 */
#define ALT_MON_GPIO_INT_POL_NSP_E_ACTLOW   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_NSP
 * 
 * Active high
 */
#define ALT_MON_GPIO_INT_POL_NSP_E_ACTHIGH  0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INT_POL_NSP register field. */
#define ALT_MON_GPIO_INT_POL_NSP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INT_POL_NSP register field. */
#define ALT_MON_GPIO_INT_POL_NSP_MSB        9
/* The width in bits of the ALT_MON_GPIO_INT_POL_NSP register field. */
#define ALT_MON_GPIO_INT_POL_NSP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INT_POL_NSP register field value. */
#define ALT_MON_GPIO_INT_POL_NSP_SET_MSK    0x00000200
/* The mask used to clear the ALT_MON_GPIO_INT_POL_NSP register field value. */
#define ALT_MON_GPIO_INT_POL_NSP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_MON_GPIO_INT_POL_NSP register field. */
#define ALT_MON_GPIO_INT_POL_NSP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INT_POL_NSP field value from a register. */
#define ALT_MON_GPIO_INT_POL_NSP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_MON_GPIO_INT_POL_NSP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INT_POL_NSP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Polarity Control Field (CONF_DONE Pin) - cdp
 * 
 * Controls the polarity of edge or level sensitivity for CONF_DONE Pin
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description
 * :-----------------------------------|:------|:------------
 *  ALT_MON_GPIO_INT_POL_CDP_E_ACTLOW  | 0x0   | Active low 
 *  ALT_MON_GPIO_INT_POL_CDP_E_ACTHIGH | 0x1   | Active high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_CDP
 * 
 * Active low
 */
#define ALT_MON_GPIO_INT_POL_CDP_E_ACTLOW   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_CDP
 * 
 * Active high
 */
#define ALT_MON_GPIO_INT_POL_CDP_E_ACTHIGH  0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INT_POL_CDP register field. */
#define ALT_MON_GPIO_INT_POL_CDP_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INT_POL_CDP register field. */
#define ALT_MON_GPIO_INT_POL_CDP_MSB        10
/* The width in bits of the ALT_MON_GPIO_INT_POL_CDP register field. */
#define ALT_MON_GPIO_INT_POL_CDP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INT_POL_CDP register field value. */
#define ALT_MON_GPIO_INT_POL_CDP_SET_MSK    0x00000400
/* The mask used to clear the ALT_MON_GPIO_INT_POL_CDP register field value. */
#define ALT_MON_GPIO_INT_POL_CDP_CLR_MSK    0xfffffbff
/* The reset value of the ALT_MON_GPIO_INT_POL_CDP register field. */
#define ALT_MON_GPIO_INT_POL_CDP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INT_POL_CDP field value from a register. */
#define ALT_MON_GPIO_INT_POL_CDP_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_MON_GPIO_INT_POL_CDP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INT_POL_CDP_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Polarity Control Field (FPGA_POWER_ON) - fpo
 * 
 * Controls the polarity of edge or level sensitivity for FPGA_POWER_ON
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description
 * :-----------------------------------|:------|:------------
 *  ALT_MON_GPIO_INT_POL_FPO_E_ACTLOW  | 0x0   | Active low 
 *  ALT_MON_GPIO_INT_POL_FPO_E_ACTHIGH | 0x1   | Active high
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_FPO
 * 
 * Active low
 */
#define ALT_MON_GPIO_INT_POL_FPO_E_ACTLOW   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INT_POL_FPO
 * 
 * Active high
 */
#define ALT_MON_GPIO_INT_POL_FPO_E_ACTHIGH  0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INT_POL_FPO register field. */
#define ALT_MON_GPIO_INT_POL_FPO_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INT_POL_FPO register field. */
#define ALT_MON_GPIO_INT_POL_FPO_MSB        11
/* The width in bits of the ALT_MON_GPIO_INT_POL_FPO register field. */
#define ALT_MON_GPIO_INT_POL_FPO_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INT_POL_FPO register field value. */
#define ALT_MON_GPIO_INT_POL_FPO_SET_MSK    0x00000800
/* The mask used to clear the ALT_MON_GPIO_INT_POL_FPO register field value. */
#define ALT_MON_GPIO_INT_POL_FPO_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_MON_GPIO_INT_POL_FPO register field. */
#define ALT_MON_GPIO_INT_POL_FPO_RESET      0x0
/* Extracts the ALT_MON_GPIO_INT_POL_FPO field value from a register. */
#define ALT_MON_GPIO_INT_POL_FPO_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_MON_GPIO_INT_POL_FPO register field value suitable for setting the register. */
#define ALT_MON_GPIO_INT_POL_FPO_SET(value) (((value) << 11) & 0x00000800)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_MON_GPIO_INT_POL.
 */
struct ALT_MON_GPIO_INT_POL_s
{
    uint32_t  ns  :  1;  /* Polarity Control Field (nSTATUS) */
    uint32_t  cd  :  1;  /* Polarity Control Field (CONF_DONE) */
    uint32_t  id  :  1;  /* Polarity Control Field (INIT_DONE) */
    uint32_t  crc :  1;  /* Polarity Control Field (CRC_ERROR) */
    uint32_t  ccd :  1;  /* Polarity Control Field (CVP_CONF_DONE) */
    uint32_t  prr :  1;  /* Polarity Control Field (PR_READY) */
    uint32_t  pre :  1;  /* Polarity Control Field (PR_ERROR) */
    uint32_t  prd :  1;  /* Polarity Control Field (PR_DONE) */
    uint32_t  ncp :  1;  /* Polarity Control Field (nCONFIG Pin) */
    uint32_t  nsp :  1;  /* Polarity Control Field (nSTATUS Pin) */
    uint32_t  cdp :  1;  /* Polarity Control Field (CONF_DONE Pin) */
    uint32_t  fpo :  1;  /* Polarity Control Field (FPGA_POWER_ON) */
    uint32_t      : 20;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_MON_GPIO_INT_POL. */
typedef volatile struct ALT_MON_GPIO_INT_POL_s  ALT_MON_GPIO_INT_POL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_MON_GPIO_INT_POL register from the beginning of the component. */
#define ALT_MON_GPIO_INT_POL_OFST        0x3c
/* The address of the ALT_MON_GPIO_INT_POL register. */
#define ALT_MON_GPIO_INT_POL_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_MON_GPIO_INT_POL_OFST))

/*
 * Register : Interrupt Status Register - gpio_intstatus
 * 
 * Reports on interrupt status for each GPIO input. The interrupt status includes
 * the effects of masking.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                           
 * :--------|:-------|:------|:---------------------------------------
 *  [0]     | R      | 0x0   | Interrupt Status Field (nSTATUS)      
 *  [1]     | R      | 0x0   | Interrupt Status Field (CONF_DONE)    
 *  [2]     | R      | 0x0   | Interrupt Status Field (INIT_DONE)    
 *  [3]     | R      | 0x0   | Interrupt Status Field (CRC_ERROR)    
 *  [4]     | R      | 0x0   | Interrupt Status Field (CVP_CONF_DONE)
 *  [5]     | R      | 0x0   | Interrupt Status Field (PR_READY)     
 *  [6]     | R      | 0x0   | Interrupt Status Field (PR_ERROR)     
 *  [7]     | R      | 0x0   | Interrupt Status Field (PR_DONE)      
 *  [8]     | R      | 0x0   | Interrupt Status Field (nCONFIG Pin)  
 *  [9]     | R      | 0x0   | Interrupt Status Field (nSTATUS Pin)  
 *  [10]    | R      | 0x0   | Interrupt Status Field (CONF_DONE Pin)
 *  [11]    | R      | 0x0   | Interrupt Status Field (FPGA_POWER_ON)
 *  [31:12] | ???    | 0x0   | *UNDEFINED*                           
 * 
 */
/*
 * Field : Interrupt Status Field (nSTATUS) - ns
 * 
 * Indicates whether nSTATUS has an active interrupt or not (after masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description
 * :--------------------------------|:------|:------------
 *  ALT_MON_GPIO_INTSTAT_NS_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_INTSTAT_NS_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_NS
 * 
 * Inactive
 */
#define ALT_MON_GPIO_INTSTAT_NS_E_INACT 0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_NS
 * 
 * Active
 */
#define ALT_MON_GPIO_INTSTAT_NS_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTSTAT_NS register field. */
#define ALT_MON_GPIO_INTSTAT_NS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTSTAT_NS register field. */
#define ALT_MON_GPIO_INTSTAT_NS_MSB        0
/* The width in bits of the ALT_MON_GPIO_INTSTAT_NS register field. */
#define ALT_MON_GPIO_INTSTAT_NS_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTSTAT_NS register field value. */
#define ALT_MON_GPIO_INTSTAT_NS_SET_MSK    0x00000001
/* The mask used to clear the ALT_MON_GPIO_INTSTAT_NS register field value. */
#define ALT_MON_GPIO_INTSTAT_NS_CLR_MSK    0xfffffffe
/* The reset value of the ALT_MON_GPIO_INTSTAT_NS register field. */
#define ALT_MON_GPIO_INTSTAT_NS_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTSTAT_NS field value from a register. */
#define ALT_MON_GPIO_INTSTAT_NS_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_MON_GPIO_INTSTAT_NS register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTSTAT_NS_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Interrupt Status Field (CONF_DONE) - cd
 * 
 * Indicates whether CONF_DONE has an active interrupt or not (after masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description
 * :--------------------------------|:------|:------------
 *  ALT_MON_GPIO_INTSTAT_CD_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_INTSTAT_CD_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_CD
 * 
 * Inactive
 */
#define ALT_MON_GPIO_INTSTAT_CD_E_INACT 0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_CD
 * 
 * Active
 */
#define ALT_MON_GPIO_INTSTAT_CD_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTSTAT_CD register field. */
#define ALT_MON_GPIO_INTSTAT_CD_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTSTAT_CD register field. */
#define ALT_MON_GPIO_INTSTAT_CD_MSB        1
/* The width in bits of the ALT_MON_GPIO_INTSTAT_CD register field. */
#define ALT_MON_GPIO_INTSTAT_CD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTSTAT_CD register field value. */
#define ALT_MON_GPIO_INTSTAT_CD_SET_MSK    0x00000002
/* The mask used to clear the ALT_MON_GPIO_INTSTAT_CD register field value. */
#define ALT_MON_GPIO_INTSTAT_CD_CLR_MSK    0xfffffffd
/* The reset value of the ALT_MON_GPIO_INTSTAT_CD register field. */
#define ALT_MON_GPIO_INTSTAT_CD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTSTAT_CD field value from a register. */
#define ALT_MON_GPIO_INTSTAT_CD_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_MON_GPIO_INTSTAT_CD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTSTAT_CD_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Interrupt Status Field (INIT_DONE) - id
 * 
 * Indicates whether INIT_DONE has an active interrupt or not (after masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description
 * :--------------------------------|:------|:------------
 *  ALT_MON_GPIO_INTSTAT_ID_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_INTSTAT_ID_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_ID
 * 
 * Inactive
 */
#define ALT_MON_GPIO_INTSTAT_ID_E_INACT 0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_ID
 * 
 * Active
 */
#define ALT_MON_GPIO_INTSTAT_ID_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTSTAT_ID register field. */
#define ALT_MON_GPIO_INTSTAT_ID_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTSTAT_ID register field. */
#define ALT_MON_GPIO_INTSTAT_ID_MSB        2
/* The width in bits of the ALT_MON_GPIO_INTSTAT_ID register field. */
#define ALT_MON_GPIO_INTSTAT_ID_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTSTAT_ID register field value. */
#define ALT_MON_GPIO_INTSTAT_ID_SET_MSK    0x00000004
/* The mask used to clear the ALT_MON_GPIO_INTSTAT_ID register field value. */
#define ALT_MON_GPIO_INTSTAT_ID_CLR_MSK    0xfffffffb
/* The reset value of the ALT_MON_GPIO_INTSTAT_ID register field. */
#define ALT_MON_GPIO_INTSTAT_ID_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTSTAT_ID field value from a register. */
#define ALT_MON_GPIO_INTSTAT_ID_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_MON_GPIO_INTSTAT_ID register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTSTAT_ID_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Interrupt Status Field (CRC_ERROR) - crc
 * 
 * Indicates whether CRC_ERROR has an active interrupt or not (after masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description
 * :---------------------------------|:------|:------------
 *  ALT_MON_GPIO_INTSTAT_CRC_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_INTSTAT_CRC_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_CRC
 * 
 * Inactive
 */
#define ALT_MON_GPIO_INTSTAT_CRC_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_CRC
 * 
 * Active
 */
#define ALT_MON_GPIO_INTSTAT_CRC_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTSTAT_CRC register field. */
#define ALT_MON_GPIO_INTSTAT_CRC_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTSTAT_CRC register field. */
#define ALT_MON_GPIO_INTSTAT_CRC_MSB        3
/* The width in bits of the ALT_MON_GPIO_INTSTAT_CRC register field. */
#define ALT_MON_GPIO_INTSTAT_CRC_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTSTAT_CRC register field value. */
#define ALT_MON_GPIO_INTSTAT_CRC_SET_MSK    0x00000008
/* The mask used to clear the ALT_MON_GPIO_INTSTAT_CRC register field value. */
#define ALT_MON_GPIO_INTSTAT_CRC_CLR_MSK    0xfffffff7
/* The reset value of the ALT_MON_GPIO_INTSTAT_CRC register field. */
#define ALT_MON_GPIO_INTSTAT_CRC_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTSTAT_CRC field value from a register. */
#define ALT_MON_GPIO_INTSTAT_CRC_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_MON_GPIO_INTSTAT_CRC register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTSTAT_CRC_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Interrupt Status Field (CVP_CONF_DONE) - ccd
 * 
 * Indicates whether CVP_CONF_DONE has an active interrupt or not (after masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description
 * :---------------------------------|:------|:------------
 *  ALT_MON_GPIO_INTSTAT_CCD_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_INTSTAT_CCD_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_CCD
 * 
 * Inactive
 */
#define ALT_MON_GPIO_INTSTAT_CCD_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_CCD
 * 
 * Active
 */
#define ALT_MON_GPIO_INTSTAT_CCD_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTSTAT_CCD register field. */
#define ALT_MON_GPIO_INTSTAT_CCD_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTSTAT_CCD register field. */
#define ALT_MON_GPIO_INTSTAT_CCD_MSB        4
/* The width in bits of the ALT_MON_GPIO_INTSTAT_CCD register field. */
#define ALT_MON_GPIO_INTSTAT_CCD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTSTAT_CCD register field value. */
#define ALT_MON_GPIO_INTSTAT_CCD_SET_MSK    0x00000010
/* The mask used to clear the ALT_MON_GPIO_INTSTAT_CCD register field value. */
#define ALT_MON_GPIO_INTSTAT_CCD_CLR_MSK    0xffffffef
/* The reset value of the ALT_MON_GPIO_INTSTAT_CCD register field. */
#define ALT_MON_GPIO_INTSTAT_CCD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTSTAT_CCD field value from a register. */
#define ALT_MON_GPIO_INTSTAT_CCD_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_MON_GPIO_INTSTAT_CCD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTSTAT_CCD_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Interrupt Status Field (PR_READY) - prr
 * 
 * Indicates whether PR_READY has an active interrupt or not (after masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description
 * :---------------------------------|:------|:------------
 *  ALT_MON_GPIO_INTSTAT_PRR_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_INTSTAT_PRR_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_PRR
 * 
 * Inactive
 */
#define ALT_MON_GPIO_INTSTAT_PRR_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_PRR
 * 
 * Active
 */
#define ALT_MON_GPIO_INTSTAT_PRR_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTSTAT_PRR register field. */
#define ALT_MON_GPIO_INTSTAT_PRR_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTSTAT_PRR register field. */
#define ALT_MON_GPIO_INTSTAT_PRR_MSB        5
/* The width in bits of the ALT_MON_GPIO_INTSTAT_PRR register field. */
#define ALT_MON_GPIO_INTSTAT_PRR_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTSTAT_PRR register field value. */
#define ALT_MON_GPIO_INTSTAT_PRR_SET_MSK    0x00000020
/* The mask used to clear the ALT_MON_GPIO_INTSTAT_PRR register field value. */
#define ALT_MON_GPIO_INTSTAT_PRR_CLR_MSK    0xffffffdf
/* The reset value of the ALT_MON_GPIO_INTSTAT_PRR register field. */
#define ALT_MON_GPIO_INTSTAT_PRR_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTSTAT_PRR field value from a register. */
#define ALT_MON_GPIO_INTSTAT_PRR_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_MON_GPIO_INTSTAT_PRR register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTSTAT_PRR_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Interrupt Status Field (PR_ERROR) - pre
 * 
 * Indicates whether PR_ERROR has an active interrupt or not (after masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description
 * :---------------------------------|:------|:------------
 *  ALT_MON_GPIO_INTSTAT_PRE_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_INTSTAT_PRE_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_PRE
 * 
 * Inactive
 */
#define ALT_MON_GPIO_INTSTAT_PRE_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_PRE
 * 
 * Active
 */
#define ALT_MON_GPIO_INTSTAT_PRE_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTSTAT_PRE register field. */
#define ALT_MON_GPIO_INTSTAT_PRE_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTSTAT_PRE register field. */
#define ALT_MON_GPIO_INTSTAT_PRE_MSB        6
/* The width in bits of the ALT_MON_GPIO_INTSTAT_PRE register field. */
#define ALT_MON_GPIO_INTSTAT_PRE_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTSTAT_PRE register field value. */
#define ALT_MON_GPIO_INTSTAT_PRE_SET_MSK    0x00000040
/* The mask used to clear the ALT_MON_GPIO_INTSTAT_PRE register field value. */
#define ALT_MON_GPIO_INTSTAT_PRE_CLR_MSK    0xffffffbf
/* The reset value of the ALT_MON_GPIO_INTSTAT_PRE register field. */
#define ALT_MON_GPIO_INTSTAT_PRE_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTSTAT_PRE field value from a register. */
#define ALT_MON_GPIO_INTSTAT_PRE_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_MON_GPIO_INTSTAT_PRE register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTSTAT_PRE_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Interrupt Status Field (PR_DONE) - prd
 * 
 * Indicates whether PR_DONE has an active interrupt or not (after masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description
 * :---------------------------------|:------|:------------
 *  ALT_MON_GPIO_INTSTAT_PRD_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_INTSTAT_PRD_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_PRD
 * 
 * Inactive
 */
#define ALT_MON_GPIO_INTSTAT_PRD_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_PRD
 * 
 * Active
 */
#define ALT_MON_GPIO_INTSTAT_PRD_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTSTAT_PRD register field. */
#define ALT_MON_GPIO_INTSTAT_PRD_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTSTAT_PRD register field. */
#define ALT_MON_GPIO_INTSTAT_PRD_MSB        7
/* The width in bits of the ALT_MON_GPIO_INTSTAT_PRD register field. */
#define ALT_MON_GPIO_INTSTAT_PRD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTSTAT_PRD register field value. */
#define ALT_MON_GPIO_INTSTAT_PRD_SET_MSK    0x00000080
/* The mask used to clear the ALT_MON_GPIO_INTSTAT_PRD register field value. */
#define ALT_MON_GPIO_INTSTAT_PRD_CLR_MSK    0xffffff7f
/* The reset value of the ALT_MON_GPIO_INTSTAT_PRD register field. */
#define ALT_MON_GPIO_INTSTAT_PRD_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTSTAT_PRD field value from a register. */
#define ALT_MON_GPIO_INTSTAT_PRD_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_MON_GPIO_INTSTAT_PRD register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTSTAT_PRD_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Interrupt Status Field (nCONFIG Pin) - ncp
 * 
 * Indicates whether nCONFIG Pin has an active interrupt or not (after masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description
 * :---------------------------------|:------|:------------
 *  ALT_MON_GPIO_INTSTAT_NCP_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_INTSTAT_NCP_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_NCP
 * 
 * Inactive
 */
#define ALT_MON_GPIO_INTSTAT_NCP_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_NCP
 * 
 * Active
 */
#define ALT_MON_GPIO_INTSTAT_NCP_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTSTAT_NCP register field. */
#define ALT_MON_GPIO_INTSTAT_NCP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTSTAT_NCP register field. */
#define ALT_MON_GPIO_INTSTAT_NCP_MSB        8
/* The width in bits of the ALT_MON_GPIO_INTSTAT_NCP register field. */
#define ALT_MON_GPIO_INTSTAT_NCP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTSTAT_NCP register field value. */
#define ALT_MON_GPIO_INTSTAT_NCP_SET_MSK    0x00000100
/* The mask used to clear the ALT_MON_GPIO_INTSTAT_NCP register field value. */
#define ALT_MON_GPIO_INTSTAT_NCP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_MON_GPIO_INTSTAT_NCP register field. */
#define ALT_MON_GPIO_INTSTAT_NCP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTSTAT_NCP field value from a register. */
#define ALT_MON_GPIO_INTSTAT_NCP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_MON_GPIO_INTSTAT_NCP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTSTAT_NCP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Interrupt Status Field (nSTATUS Pin) - nsp
 * 
 * Indicates whether nSTATUS Pin has an active interrupt or not (after masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description
 * :---------------------------------|:------|:------------
 *  ALT_MON_GPIO_INTSTAT_NSP_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_INTSTAT_NSP_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_NSP
 * 
 * Inactive
 */
#define ALT_MON_GPIO_INTSTAT_NSP_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_NSP
 * 
 * Active
 */
#define ALT_MON_GPIO_INTSTAT_NSP_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTSTAT_NSP register field. */
#define ALT_MON_GPIO_INTSTAT_NSP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTSTAT_NSP register field. */
#define ALT_MON_GPIO_INTSTAT_NSP_MSB        9
/* The width in bits of the ALT_MON_GPIO_INTSTAT_NSP register field. */
#define ALT_MON_GPIO_INTSTAT_NSP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTSTAT_NSP register field value. */
#define ALT_MON_GPIO_INTSTAT_NSP_SET_MSK    0x00000200
/* The mask used to clear the ALT_MON_GPIO_INTSTAT_NSP register field value. */
#define ALT_MON_GPIO_INTSTAT_NSP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_MON_GPIO_INTSTAT_NSP register field. */
#define ALT_MON_GPIO_INTSTAT_NSP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTSTAT_NSP field value from a register. */
#define ALT_MON_GPIO_INTSTAT_NSP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_MON_GPIO_INTSTAT_NSP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTSTAT_NSP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Interrupt Status Field (CONF_DONE Pin) - cdp
 * 
 * Indicates whether CONF_DONE Pin has an active interrupt or not (after masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description
 * :---------------------------------|:------|:------------
 *  ALT_MON_GPIO_INTSTAT_CDP_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_INTSTAT_CDP_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_CDP
 * 
 * Inactive
 */
#define ALT_MON_GPIO_INTSTAT_CDP_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_CDP
 * 
 * Active
 */
#define ALT_MON_GPIO_INTSTAT_CDP_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTSTAT_CDP register field. */
#define ALT_MON_GPIO_INTSTAT_CDP_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTSTAT_CDP register field. */
#define ALT_MON_GPIO_INTSTAT_CDP_MSB        10
/* The width in bits of the ALT_MON_GPIO_INTSTAT_CDP register field. */
#define ALT_MON_GPIO_INTSTAT_CDP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTSTAT_CDP register field value. */
#define ALT_MON_GPIO_INTSTAT_CDP_SET_MSK    0x00000400
/* The mask used to clear the ALT_MON_GPIO_INTSTAT_CDP register field value. */
#define ALT_MON_GPIO_INTSTAT_CDP_CLR_MSK    0xfffffbff
/* The reset value of the ALT_MON_GPIO_INTSTAT_CDP register field. */
#define ALT_MON_GPIO_INTSTAT_CDP_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTSTAT_CDP field value from a register. */
#define ALT_MON_GPIO_INTSTAT_CDP_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_MON_GPIO_INTSTAT_CDP register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTSTAT_CDP_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Interrupt Status Field (FPGA_POWER_ON) - fpo
 * 
 * Indicates whether FPGA_POWER_ON has an active interrupt or not (after masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description
 * :---------------------------------|:------|:------------
 *  ALT_MON_GPIO_INTSTAT_FPO_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_INTSTAT_FPO_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_FPO
 * 
 * Inactive
 */
#define ALT_MON_GPIO_INTSTAT_FPO_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_INTSTAT_FPO
 * 
 * Active
 */
#define ALT_MON_GPIO_INTSTAT_FPO_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_INTSTAT_FPO register field. */
#define ALT_MON_GPIO_INTSTAT_FPO_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_INTSTAT_FPO register field. */
#define ALT_MON_GPIO_INTSTAT_FPO_MSB        11
/* The width in bits of the ALT_MON_GPIO_INTSTAT_FPO register field. */
#define ALT_MON_GPIO_INTSTAT_FPO_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_INTSTAT_FPO register field value. */
#define ALT_MON_GPIO_INTSTAT_FPO_SET_MSK    0x00000800
/* The mask used to clear the ALT_MON_GPIO_INTSTAT_FPO register field value. */
#define ALT_MON_GPIO_INTSTAT_FPO_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_MON_GPIO_INTSTAT_FPO register field. */
#define ALT_MON_GPIO_INTSTAT_FPO_RESET      0x0
/* Extracts the ALT_MON_GPIO_INTSTAT_FPO field value from a register. */
#define ALT_MON_GPIO_INTSTAT_FPO_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_MON_GPIO_INTSTAT_FPO register field value suitable for setting the register. */
#define ALT_MON_GPIO_INTSTAT_FPO_SET(value) (((value) << 11) & 0x00000800)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_MON_GPIO_INTSTAT.
 */
struct ALT_MON_GPIO_INTSTAT_s
{
    const uint32_t  ns  :  1;  /* Interrupt Status Field (nSTATUS) */
    const uint32_t  cd  :  1;  /* Interrupt Status Field (CONF_DONE) */
    const uint32_t  id  :  1;  /* Interrupt Status Field (INIT_DONE) */
    const uint32_t  crc :  1;  /* Interrupt Status Field (CRC_ERROR) */
    const uint32_t  ccd :  1;  /* Interrupt Status Field (CVP_CONF_DONE) */
    const uint32_t  prr :  1;  /* Interrupt Status Field (PR_READY) */
    const uint32_t  pre :  1;  /* Interrupt Status Field (PR_ERROR) */
    const uint32_t  prd :  1;  /* Interrupt Status Field (PR_DONE) */
    const uint32_t  ncp :  1;  /* Interrupt Status Field (nCONFIG Pin) */
    const uint32_t  nsp :  1;  /* Interrupt Status Field (nSTATUS Pin) */
    const uint32_t  cdp :  1;  /* Interrupt Status Field (CONF_DONE Pin) */
    const uint32_t  fpo :  1;  /* Interrupt Status Field (FPGA_POWER_ON) */
    uint32_t            : 20;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_MON_GPIO_INTSTAT. */
typedef volatile struct ALT_MON_GPIO_INTSTAT_s  ALT_MON_GPIO_INTSTAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_MON_GPIO_INTSTAT register from the beginning of the component. */
#define ALT_MON_GPIO_INTSTAT_OFST        0x40
/* The address of the ALT_MON_GPIO_INTSTAT register. */
#define ALT_MON_GPIO_INTSTAT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_MON_GPIO_INTSTAT_OFST))

/*
 * Register : Raw Interrupt Status Register - gpio_raw_intstatus
 * 
 * Reports on raw interrupt status for each GPIO input. The raw interrupt status
 * excludes the effects of masking.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                               
 * :--------|:-------|:------|:-------------------------------------------
 *  [0]     | R      | 0x0   | Raw Interrupt Status Field (nSTATUS)      
 *  [1]     | R      | 0x0   | Raw Interrupt Status Field (CONF_DONE)    
 *  [2]     | R      | 0x0   | Raw Interrupt Status Field (INIT_DONE)    
 *  [3]     | R      | 0x0   | Raw Interrupt Status Field (CRC_ERROR)    
 *  [4]     | R      | 0x0   | Raw Interrupt Status Field (CVP_CONF_DONE)
 *  [5]     | R      | 0x0   | Raw Interrupt Status Field (PR_READY)     
 *  [6]     | R      | 0x0   | Raw Interrupt Status Field (PR_ERROR)     
 *  [7]     | R      | 0x0   | Raw Interrupt Status Field (PR_DONE)      
 *  [8]     | R      | 0x0   | Raw Interrupt Status Field (nCONFIG Pin)  
 *  [9]     | R      | 0x0   | Raw Interrupt Status Field (nSTATUS Pin)  
 *  [10]    | R      | 0x0   | Raw Interrupt Status Field (CONF_DONE Pin)
 *  [11]    | R      | 0x0   | Raw Interrupt Status Field (FPGA_POWER_ON)
 *  [31:12] | ???    | 0x0   | *UNDEFINED*                               
 * 
 */
/*
 * Field : Raw Interrupt Status Field (nSTATUS) - ns
 * 
 * Indicates whether nSTATUS has an active interrupt or not (before masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description
 * :------------------------------------|:------|:------------
 *  ALT_MON_GPIO_RAW_INTSTAT_NS_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_RAW_INTSTAT_NS_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_NS
 * 
 * Inactive
 */
#define ALT_MON_GPIO_RAW_INTSTAT_NS_E_INACT 0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_NS
 * 
 * Active
 */
#define ALT_MON_GPIO_RAW_INTSTAT_NS_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_RAW_INTSTAT_NS register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_NS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_RAW_INTSTAT_NS register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_NS_MSB        0
/* The width in bits of the ALT_MON_GPIO_RAW_INTSTAT_NS register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_NS_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_RAW_INTSTAT_NS register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_NS_SET_MSK    0x00000001
/* The mask used to clear the ALT_MON_GPIO_RAW_INTSTAT_NS register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_NS_CLR_MSK    0xfffffffe
/* The reset value of the ALT_MON_GPIO_RAW_INTSTAT_NS register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_NS_RESET      0x0
/* Extracts the ALT_MON_GPIO_RAW_INTSTAT_NS field value from a register. */
#define ALT_MON_GPIO_RAW_INTSTAT_NS_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_MON_GPIO_RAW_INTSTAT_NS register field value suitable for setting the register. */
#define ALT_MON_GPIO_RAW_INTSTAT_NS_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Raw Interrupt Status Field (CONF_DONE) - cd
 * 
 * Indicates whether CONF_DONE has an active interrupt or not (before masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description
 * :------------------------------------|:------|:------------
 *  ALT_MON_GPIO_RAW_INTSTAT_CD_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_RAW_INTSTAT_CD_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_CD
 * 
 * Inactive
 */
#define ALT_MON_GPIO_RAW_INTSTAT_CD_E_INACT 0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_CD
 * 
 * Active
 */
#define ALT_MON_GPIO_RAW_INTSTAT_CD_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_RAW_INTSTAT_CD register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CD_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_RAW_INTSTAT_CD register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CD_MSB        1
/* The width in bits of the ALT_MON_GPIO_RAW_INTSTAT_CD register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_RAW_INTSTAT_CD register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_CD_SET_MSK    0x00000002
/* The mask used to clear the ALT_MON_GPIO_RAW_INTSTAT_CD register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_CD_CLR_MSK    0xfffffffd
/* The reset value of the ALT_MON_GPIO_RAW_INTSTAT_CD register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CD_RESET      0x0
/* Extracts the ALT_MON_GPIO_RAW_INTSTAT_CD field value from a register. */
#define ALT_MON_GPIO_RAW_INTSTAT_CD_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_MON_GPIO_RAW_INTSTAT_CD register field value suitable for setting the register. */
#define ALT_MON_GPIO_RAW_INTSTAT_CD_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Raw Interrupt Status Field (INIT_DONE) - id
 * 
 * Indicates whether INIT_DONE has an active interrupt or not (before masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description
 * :------------------------------------|:------|:------------
 *  ALT_MON_GPIO_RAW_INTSTAT_ID_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_RAW_INTSTAT_ID_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_ID
 * 
 * Inactive
 */
#define ALT_MON_GPIO_RAW_INTSTAT_ID_E_INACT 0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_ID
 * 
 * Active
 */
#define ALT_MON_GPIO_RAW_INTSTAT_ID_E_ACT   0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_RAW_INTSTAT_ID register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_ID_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_RAW_INTSTAT_ID register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_ID_MSB        2
/* The width in bits of the ALT_MON_GPIO_RAW_INTSTAT_ID register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_ID_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_RAW_INTSTAT_ID register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_ID_SET_MSK    0x00000004
/* The mask used to clear the ALT_MON_GPIO_RAW_INTSTAT_ID register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_ID_CLR_MSK    0xfffffffb
/* The reset value of the ALT_MON_GPIO_RAW_INTSTAT_ID register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_ID_RESET      0x0
/* Extracts the ALT_MON_GPIO_RAW_INTSTAT_ID field value from a register. */
#define ALT_MON_GPIO_RAW_INTSTAT_ID_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_MON_GPIO_RAW_INTSTAT_ID register field value suitable for setting the register. */
#define ALT_MON_GPIO_RAW_INTSTAT_ID_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Raw Interrupt Status Field (CRC_ERROR) - crc
 * 
 * Indicates whether CRC_ERROR has an active interrupt or not (before masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description
 * :-------------------------------------|:------|:------------
 *  ALT_MON_GPIO_RAW_INTSTAT_CRC_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_RAW_INTSTAT_CRC_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_CRC
 * 
 * Inactive
 */
#define ALT_MON_GPIO_RAW_INTSTAT_CRC_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_CRC
 * 
 * Active
 */
#define ALT_MON_GPIO_RAW_INTSTAT_CRC_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_RAW_INTSTAT_CRC register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CRC_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_RAW_INTSTAT_CRC register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CRC_MSB        3
/* The width in bits of the ALT_MON_GPIO_RAW_INTSTAT_CRC register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CRC_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_RAW_INTSTAT_CRC register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_CRC_SET_MSK    0x00000008
/* The mask used to clear the ALT_MON_GPIO_RAW_INTSTAT_CRC register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_CRC_CLR_MSK    0xfffffff7
/* The reset value of the ALT_MON_GPIO_RAW_INTSTAT_CRC register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CRC_RESET      0x0
/* Extracts the ALT_MON_GPIO_RAW_INTSTAT_CRC field value from a register. */
#define ALT_MON_GPIO_RAW_INTSTAT_CRC_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_MON_GPIO_RAW_INTSTAT_CRC register field value suitable for setting the register. */
#define ALT_MON_GPIO_RAW_INTSTAT_CRC_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Raw Interrupt Status Field (CVP_CONF_DONE) - ccd
 * 
 * Indicates whether CVP_CONF_DONE has an active interrupt or not (before masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description
 * :-------------------------------------|:------|:------------
 *  ALT_MON_GPIO_RAW_INTSTAT_CCD_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_RAW_INTSTAT_CCD_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_CCD
 * 
 * Inactive
 */
#define ALT_MON_GPIO_RAW_INTSTAT_CCD_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_CCD
 * 
 * Active
 */
#define ALT_MON_GPIO_RAW_INTSTAT_CCD_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_RAW_INTSTAT_CCD register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CCD_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_RAW_INTSTAT_CCD register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CCD_MSB        4
/* The width in bits of the ALT_MON_GPIO_RAW_INTSTAT_CCD register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CCD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_RAW_INTSTAT_CCD register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_CCD_SET_MSK    0x00000010
/* The mask used to clear the ALT_MON_GPIO_RAW_INTSTAT_CCD register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_CCD_CLR_MSK    0xffffffef
/* The reset value of the ALT_MON_GPIO_RAW_INTSTAT_CCD register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CCD_RESET      0x0
/* Extracts the ALT_MON_GPIO_RAW_INTSTAT_CCD field value from a register. */
#define ALT_MON_GPIO_RAW_INTSTAT_CCD_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_MON_GPIO_RAW_INTSTAT_CCD register field value suitable for setting the register. */
#define ALT_MON_GPIO_RAW_INTSTAT_CCD_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Raw Interrupt Status Field (PR_READY) - prr
 * 
 * Indicates whether PR_READY has an active interrupt or not (before masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description
 * :-------------------------------------|:------|:------------
 *  ALT_MON_GPIO_RAW_INTSTAT_PRR_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_RAW_INTSTAT_PRR_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_PRR
 * 
 * Inactive
 */
#define ALT_MON_GPIO_RAW_INTSTAT_PRR_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_PRR
 * 
 * Active
 */
#define ALT_MON_GPIO_RAW_INTSTAT_PRR_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_RAW_INTSTAT_PRR register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRR_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_RAW_INTSTAT_PRR register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRR_MSB        5
/* The width in bits of the ALT_MON_GPIO_RAW_INTSTAT_PRR register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRR_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_RAW_INTSTAT_PRR register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRR_SET_MSK    0x00000020
/* The mask used to clear the ALT_MON_GPIO_RAW_INTSTAT_PRR register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRR_CLR_MSK    0xffffffdf
/* The reset value of the ALT_MON_GPIO_RAW_INTSTAT_PRR register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRR_RESET      0x0
/* Extracts the ALT_MON_GPIO_RAW_INTSTAT_PRR field value from a register. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRR_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_MON_GPIO_RAW_INTSTAT_PRR register field value suitable for setting the register. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRR_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Raw Interrupt Status Field (PR_ERROR) - pre
 * 
 * Indicates whether PR_ERROR has an active interrupt or not (before masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description
 * :-------------------------------------|:------|:------------
 *  ALT_MON_GPIO_RAW_INTSTAT_PRE_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_RAW_INTSTAT_PRE_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_PRE
 * 
 * Inactive
 */
#define ALT_MON_GPIO_RAW_INTSTAT_PRE_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_PRE
 * 
 * Active
 */
#define ALT_MON_GPIO_RAW_INTSTAT_PRE_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_RAW_INTSTAT_PRE register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRE_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_RAW_INTSTAT_PRE register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRE_MSB        6
/* The width in bits of the ALT_MON_GPIO_RAW_INTSTAT_PRE register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRE_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_RAW_INTSTAT_PRE register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRE_SET_MSK    0x00000040
/* The mask used to clear the ALT_MON_GPIO_RAW_INTSTAT_PRE register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRE_CLR_MSK    0xffffffbf
/* The reset value of the ALT_MON_GPIO_RAW_INTSTAT_PRE register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRE_RESET      0x0
/* Extracts the ALT_MON_GPIO_RAW_INTSTAT_PRE field value from a register. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRE_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_MON_GPIO_RAW_INTSTAT_PRE register field value suitable for setting the register. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRE_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Raw Interrupt Status Field (PR_DONE) - prd
 * 
 * Indicates whether PR_DONE has an active interrupt or not (before masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description
 * :-------------------------------------|:------|:------------
 *  ALT_MON_GPIO_RAW_INTSTAT_PRD_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_RAW_INTSTAT_PRD_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_PRD
 * 
 * Inactive
 */
#define ALT_MON_GPIO_RAW_INTSTAT_PRD_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_PRD
 * 
 * Active
 */
#define ALT_MON_GPIO_RAW_INTSTAT_PRD_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_RAW_INTSTAT_PRD register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRD_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_RAW_INTSTAT_PRD register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRD_MSB        7
/* The width in bits of the ALT_MON_GPIO_RAW_INTSTAT_PRD register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_RAW_INTSTAT_PRD register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRD_SET_MSK    0x00000080
/* The mask used to clear the ALT_MON_GPIO_RAW_INTSTAT_PRD register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRD_CLR_MSK    0xffffff7f
/* The reset value of the ALT_MON_GPIO_RAW_INTSTAT_PRD register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRD_RESET      0x0
/* Extracts the ALT_MON_GPIO_RAW_INTSTAT_PRD field value from a register. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRD_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_MON_GPIO_RAW_INTSTAT_PRD register field value suitable for setting the register. */
#define ALT_MON_GPIO_RAW_INTSTAT_PRD_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Raw Interrupt Status Field (nCONFIG Pin) - ncp
 * 
 * Indicates whether nCONFIG Pin has an active interrupt or not (before masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description
 * :-------------------------------------|:------|:------------
 *  ALT_MON_GPIO_RAW_INTSTAT_NCP_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_RAW_INTSTAT_NCP_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_NCP
 * 
 * Inactive
 */
#define ALT_MON_GPIO_RAW_INTSTAT_NCP_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_NCP
 * 
 * Active
 */
#define ALT_MON_GPIO_RAW_INTSTAT_NCP_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_RAW_INTSTAT_NCP register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_NCP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_RAW_INTSTAT_NCP register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_NCP_MSB        8
/* The width in bits of the ALT_MON_GPIO_RAW_INTSTAT_NCP register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_NCP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_RAW_INTSTAT_NCP register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_NCP_SET_MSK    0x00000100
/* The mask used to clear the ALT_MON_GPIO_RAW_INTSTAT_NCP register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_NCP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_MON_GPIO_RAW_INTSTAT_NCP register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_NCP_RESET      0x0
/* Extracts the ALT_MON_GPIO_RAW_INTSTAT_NCP field value from a register. */
#define ALT_MON_GPIO_RAW_INTSTAT_NCP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_MON_GPIO_RAW_INTSTAT_NCP register field value suitable for setting the register. */
#define ALT_MON_GPIO_RAW_INTSTAT_NCP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Raw Interrupt Status Field (nSTATUS Pin) - nsp
 * 
 * Indicates whether nSTATUS Pin has an active interrupt or not (before masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description
 * :-------------------------------------|:------|:------------
 *  ALT_MON_GPIO_RAW_INTSTAT_NSP_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_RAW_INTSTAT_NSP_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_NSP
 * 
 * Inactive
 */
#define ALT_MON_GPIO_RAW_INTSTAT_NSP_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_NSP
 * 
 * Active
 */
#define ALT_MON_GPIO_RAW_INTSTAT_NSP_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_RAW_INTSTAT_NSP register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_NSP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_RAW_INTSTAT_NSP register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_NSP_MSB        9
/* The width in bits of the ALT_MON_GPIO_RAW_INTSTAT_NSP register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_NSP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_RAW_INTSTAT_NSP register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_NSP_SET_MSK    0x00000200
/* The mask used to clear the ALT_MON_GPIO_RAW_INTSTAT_NSP register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_NSP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_MON_GPIO_RAW_INTSTAT_NSP register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_NSP_RESET      0x0
/* Extracts the ALT_MON_GPIO_RAW_INTSTAT_NSP field value from a register. */
#define ALT_MON_GPIO_RAW_INTSTAT_NSP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_MON_GPIO_RAW_INTSTAT_NSP register field value suitable for setting the register. */
#define ALT_MON_GPIO_RAW_INTSTAT_NSP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Raw Interrupt Status Field (CONF_DONE Pin) - cdp
 * 
 * Indicates whether CONF_DONE Pin has an active interrupt or not (before masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description
 * :-------------------------------------|:------|:------------
 *  ALT_MON_GPIO_RAW_INTSTAT_CDP_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_RAW_INTSTAT_CDP_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_CDP
 * 
 * Inactive
 */
#define ALT_MON_GPIO_RAW_INTSTAT_CDP_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_CDP
 * 
 * Active
 */
#define ALT_MON_GPIO_RAW_INTSTAT_CDP_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_RAW_INTSTAT_CDP register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CDP_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_RAW_INTSTAT_CDP register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CDP_MSB        10
/* The width in bits of the ALT_MON_GPIO_RAW_INTSTAT_CDP register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CDP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_RAW_INTSTAT_CDP register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_CDP_SET_MSK    0x00000400
/* The mask used to clear the ALT_MON_GPIO_RAW_INTSTAT_CDP register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_CDP_CLR_MSK    0xfffffbff
/* The reset value of the ALT_MON_GPIO_RAW_INTSTAT_CDP register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_CDP_RESET      0x0
/* Extracts the ALT_MON_GPIO_RAW_INTSTAT_CDP field value from a register. */
#define ALT_MON_GPIO_RAW_INTSTAT_CDP_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_MON_GPIO_RAW_INTSTAT_CDP register field value suitable for setting the register. */
#define ALT_MON_GPIO_RAW_INTSTAT_CDP_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Raw Interrupt Status Field (FPGA_POWER_ON) - fpo
 * 
 * Indicates whether FPGA_POWER_ON has an active interrupt or not (before masking).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description
 * :-------------------------------------|:------|:------------
 *  ALT_MON_GPIO_RAW_INTSTAT_FPO_E_INACT | 0x0   | Inactive   
 *  ALT_MON_GPIO_RAW_INTSTAT_FPO_E_ACT   | 0x1   | Active     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_FPO
 * 
 * Inactive
 */
#define ALT_MON_GPIO_RAW_INTSTAT_FPO_E_INACT    0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_RAW_INTSTAT_FPO
 * 
 * Active
 */
#define ALT_MON_GPIO_RAW_INTSTAT_FPO_E_ACT      0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_RAW_INTSTAT_FPO register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_FPO_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_RAW_INTSTAT_FPO register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_FPO_MSB        11
/* The width in bits of the ALT_MON_GPIO_RAW_INTSTAT_FPO register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_FPO_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_RAW_INTSTAT_FPO register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_FPO_SET_MSK    0x00000800
/* The mask used to clear the ALT_MON_GPIO_RAW_INTSTAT_FPO register field value. */
#define ALT_MON_GPIO_RAW_INTSTAT_FPO_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_MON_GPIO_RAW_INTSTAT_FPO register field. */
#define ALT_MON_GPIO_RAW_INTSTAT_FPO_RESET      0x0
/* Extracts the ALT_MON_GPIO_RAW_INTSTAT_FPO field value from a register. */
#define ALT_MON_GPIO_RAW_INTSTAT_FPO_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_MON_GPIO_RAW_INTSTAT_FPO register field value suitable for setting the register. */
#define ALT_MON_GPIO_RAW_INTSTAT_FPO_SET(value) (((value) << 11) & 0x00000800)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_MON_GPIO_RAW_INTSTAT.
 */
struct ALT_MON_GPIO_RAW_INTSTAT_s
{
    const uint32_t  ns  :  1;  /* Raw Interrupt Status Field (nSTATUS) */
    const uint32_t  cd  :  1;  /* Raw Interrupt Status Field (CONF_DONE) */
    const uint32_t  id  :  1;  /* Raw Interrupt Status Field (INIT_DONE) */
    const uint32_t  crc :  1;  /* Raw Interrupt Status Field (CRC_ERROR) */
    const uint32_t  ccd :  1;  /* Raw Interrupt Status Field (CVP_CONF_DONE) */
    const uint32_t  prr :  1;  /* Raw Interrupt Status Field (PR_READY) */
    const uint32_t  pre :  1;  /* Raw Interrupt Status Field (PR_ERROR) */
    const uint32_t  prd :  1;  /* Raw Interrupt Status Field (PR_DONE) */
    const uint32_t  ncp :  1;  /* Raw Interrupt Status Field (nCONFIG Pin) */
    const uint32_t  nsp :  1;  /* Raw Interrupt Status Field (nSTATUS Pin) */
    const uint32_t  cdp :  1;  /* Raw Interrupt Status Field (CONF_DONE Pin) */
    const uint32_t  fpo :  1;  /* Raw Interrupt Status Field (FPGA_POWER_ON) */
    uint32_t            : 20;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_MON_GPIO_RAW_INTSTAT. */
typedef volatile struct ALT_MON_GPIO_RAW_INTSTAT_s  ALT_MON_GPIO_RAW_INTSTAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_MON_GPIO_RAW_INTSTAT register from the beginning of the component. */
#define ALT_MON_GPIO_RAW_INTSTAT_OFST        0x44
/* The address of the ALT_MON_GPIO_RAW_INTSTAT register. */
#define ALT_MON_GPIO_RAW_INTSTAT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_MON_GPIO_RAW_INTSTAT_OFST))

/*
 * Register : Clear Interrupt Register - gpio_porta_eoi
 * 
 * This register is written by software to clear edge interrupts generated by each
 * individual GPIO input. This register always reads back as zero.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                               
 * :--------|:-------|:------|:-------------------------------------------
 *  [0]     | W      | 0x0   | Clear Edge Interrupt Field (nSTATUS)      
 *  [1]     | W      | 0x0   | Clear Edge Interrupt Field (CONF_DONE)    
 *  [2]     | W      | 0x0   | Clear Edge Interrupt Field (INIT_DONE)    
 *  [3]     | W      | 0x0   | Clear Edge Interrupt Field (CRC_ERROR)    
 *  [4]     | W      | 0x0   | Clear Edge Interrupt Field (CVP_CONF_DONE)
 *  [5]     | W      | 0x0   | Clear Edge Interrupt Field (PR_READY)     
 *  [6]     | W      | 0x0   | Clear Edge Interrupt Field (PR_ERROR)     
 *  [7]     | W      | 0x0   | Clear Edge Interrupt Field (PR_DONE)      
 *  [8]     | W      | 0x0   | Clear Edge Interrupt Field (nCONFIG Pin)  
 *  [9]     | W      | 0x0   | Clear Edge Interrupt Field (nSTATUS Pin)  
 *  [10]    | W      | 0x0   | Clear Edge Interrupt Field (CONF_DONE Pin)
 *  [11]    | W      | 0x0   | Clear Edge Interrupt Field (FPGA_POWER_ON)
 *  [31:12] | ???    | 0x0   | *UNDEFINED*                               
 * 
 */
/*
 * Field : Clear Edge Interrupt Field (nSTATUS) - ns
 * 
 * Used by software to clear an nSTATUS edge interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description       
 * :----------------------------------|:------|:-------------------
 *  ALT_MON_GPIO_PORTA_EOI_NS_E_NOCLR | 0x0   | No interrupt clear
 *  ALT_MON_GPIO_PORTA_EOI_NS_E_CLR   | 0x1   | Clear interrupt   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_NS
 * 
 * No interrupt clear
 */
#define ALT_MON_GPIO_PORTA_EOI_NS_E_NOCLR   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_NS
 * 
 * Clear interrupt
 */
#define ALT_MON_GPIO_PORTA_EOI_NS_E_CLR     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_PORTA_EOI_NS register field. */
#define ALT_MON_GPIO_PORTA_EOI_NS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_PORTA_EOI_NS register field. */
#define ALT_MON_GPIO_PORTA_EOI_NS_MSB        0
/* The width in bits of the ALT_MON_GPIO_PORTA_EOI_NS register field. */
#define ALT_MON_GPIO_PORTA_EOI_NS_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_PORTA_EOI_NS register field value. */
#define ALT_MON_GPIO_PORTA_EOI_NS_SET_MSK    0x00000001
/* The mask used to clear the ALT_MON_GPIO_PORTA_EOI_NS register field value. */
#define ALT_MON_GPIO_PORTA_EOI_NS_CLR_MSK    0xfffffffe
/* The reset value of the ALT_MON_GPIO_PORTA_EOI_NS register field. */
#define ALT_MON_GPIO_PORTA_EOI_NS_RESET      0x0
/* Extracts the ALT_MON_GPIO_PORTA_EOI_NS field value from a register. */
#define ALT_MON_GPIO_PORTA_EOI_NS_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_MON_GPIO_PORTA_EOI_NS register field value suitable for setting the register. */
#define ALT_MON_GPIO_PORTA_EOI_NS_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Clear Edge Interrupt Field (CONF_DONE) - cd
 * 
 * Used by software to clear an CONF_DONE edge interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description       
 * :----------------------------------|:------|:-------------------
 *  ALT_MON_GPIO_PORTA_EOI_CD_E_NOCLR | 0x0   | No interrupt clear
 *  ALT_MON_GPIO_PORTA_EOI_CD_E_CLR   | 0x1   | Clear interrupt   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_CD
 * 
 * No interrupt clear
 */
#define ALT_MON_GPIO_PORTA_EOI_CD_E_NOCLR   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_CD
 * 
 * Clear interrupt
 */
#define ALT_MON_GPIO_PORTA_EOI_CD_E_CLR     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_PORTA_EOI_CD register field. */
#define ALT_MON_GPIO_PORTA_EOI_CD_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_PORTA_EOI_CD register field. */
#define ALT_MON_GPIO_PORTA_EOI_CD_MSB        1
/* The width in bits of the ALT_MON_GPIO_PORTA_EOI_CD register field. */
#define ALT_MON_GPIO_PORTA_EOI_CD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_PORTA_EOI_CD register field value. */
#define ALT_MON_GPIO_PORTA_EOI_CD_SET_MSK    0x00000002
/* The mask used to clear the ALT_MON_GPIO_PORTA_EOI_CD register field value. */
#define ALT_MON_GPIO_PORTA_EOI_CD_CLR_MSK    0xfffffffd
/* The reset value of the ALT_MON_GPIO_PORTA_EOI_CD register field. */
#define ALT_MON_GPIO_PORTA_EOI_CD_RESET      0x0
/* Extracts the ALT_MON_GPIO_PORTA_EOI_CD field value from a register. */
#define ALT_MON_GPIO_PORTA_EOI_CD_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_MON_GPIO_PORTA_EOI_CD register field value suitable for setting the register. */
#define ALT_MON_GPIO_PORTA_EOI_CD_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Clear Edge Interrupt Field (INIT_DONE) - id
 * 
 * Used by software to clear an INIT_DONE edge interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description       
 * :----------------------------------|:------|:-------------------
 *  ALT_MON_GPIO_PORTA_EOI_ID_E_NOCLR | 0x0   | No interrupt clear
 *  ALT_MON_GPIO_PORTA_EOI_ID_E_CLR   | 0x1   | Clear interrupt   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_ID
 * 
 * No interrupt clear
 */
#define ALT_MON_GPIO_PORTA_EOI_ID_E_NOCLR   0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_ID
 * 
 * Clear interrupt
 */
#define ALT_MON_GPIO_PORTA_EOI_ID_E_CLR     0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_PORTA_EOI_ID register field. */
#define ALT_MON_GPIO_PORTA_EOI_ID_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_PORTA_EOI_ID register field. */
#define ALT_MON_GPIO_PORTA_EOI_ID_MSB        2
/* The width in bits of the ALT_MON_GPIO_PORTA_EOI_ID register field. */
#define ALT_MON_GPIO_PORTA_EOI_ID_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_PORTA_EOI_ID register field value. */
#define ALT_MON_GPIO_PORTA_EOI_ID_SET_MSK    0x00000004
/* The mask used to clear the ALT_MON_GPIO_PORTA_EOI_ID register field value. */
#define ALT_MON_GPIO_PORTA_EOI_ID_CLR_MSK    0xfffffffb
/* The reset value of the ALT_MON_GPIO_PORTA_EOI_ID register field. */
#define ALT_MON_GPIO_PORTA_EOI_ID_RESET      0x0
/* Extracts the ALT_MON_GPIO_PORTA_EOI_ID field value from a register. */
#define ALT_MON_GPIO_PORTA_EOI_ID_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_MON_GPIO_PORTA_EOI_ID register field value suitable for setting the register. */
#define ALT_MON_GPIO_PORTA_EOI_ID_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Clear Edge Interrupt Field (CRC_ERROR) - crc
 * 
 * Used by software to clear an CRC_ERROR edge interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description       
 * :-----------------------------------|:------|:-------------------
 *  ALT_MON_GPIO_PORTA_EOI_CRC_E_NOCLR | 0x0   | No interrupt clear
 *  ALT_MON_GPIO_PORTA_EOI_CRC_E_CLR   | 0x1   | Clear interrupt   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_CRC
 * 
 * No interrupt clear
 */
#define ALT_MON_GPIO_PORTA_EOI_CRC_E_NOCLR  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_CRC
 * 
 * Clear interrupt
 */
#define ALT_MON_GPIO_PORTA_EOI_CRC_E_CLR    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_PORTA_EOI_CRC register field. */
#define ALT_MON_GPIO_PORTA_EOI_CRC_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_PORTA_EOI_CRC register field. */
#define ALT_MON_GPIO_PORTA_EOI_CRC_MSB        3
/* The width in bits of the ALT_MON_GPIO_PORTA_EOI_CRC register field. */
#define ALT_MON_GPIO_PORTA_EOI_CRC_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_PORTA_EOI_CRC register field value. */
#define ALT_MON_GPIO_PORTA_EOI_CRC_SET_MSK    0x00000008
/* The mask used to clear the ALT_MON_GPIO_PORTA_EOI_CRC register field value. */
#define ALT_MON_GPIO_PORTA_EOI_CRC_CLR_MSK    0xfffffff7
/* The reset value of the ALT_MON_GPIO_PORTA_EOI_CRC register field. */
#define ALT_MON_GPIO_PORTA_EOI_CRC_RESET      0x0
/* Extracts the ALT_MON_GPIO_PORTA_EOI_CRC field value from a register. */
#define ALT_MON_GPIO_PORTA_EOI_CRC_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_MON_GPIO_PORTA_EOI_CRC register field value suitable for setting the register. */
#define ALT_MON_GPIO_PORTA_EOI_CRC_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Clear Edge Interrupt Field (CVP_CONF_DONE) - ccd
 * 
 * Used by software to clear an CVP_CONF_DONE edge interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description       
 * :-----------------------------------|:------|:-------------------
 *  ALT_MON_GPIO_PORTA_EOI_CCD_E_NOCLR | 0x0   | No interrupt clear
 *  ALT_MON_GPIO_PORTA_EOI_CCD_E_CLR   | 0x1   | Clear interrupt   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_CCD
 * 
 * No interrupt clear
 */
#define ALT_MON_GPIO_PORTA_EOI_CCD_E_NOCLR  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_CCD
 * 
 * Clear interrupt
 */
#define ALT_MON_GPIO_PORTA_EOI_CCD_E_CLR    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_PORTA_EOI_CCD register field. */
#define ALT_MON_GPIO_PORTA_EOI_CCD_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_PORTA_EOI_CCD register field. */
#define ALT_MON_GPIO_PORTA_EOI_CCD_MSB        4
/* The width in bits of the ALT_MON_GPIO_PORTA_EOI_CCD register field. */
#define ALT_MON_GPIO_PORTA_EOI_CCD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_PORTA_EOI_CCD register field value. */
#define ALT_MON_GPIO_PORTA_EOI_CCD_SET_MSK    0x00000010
/* The mask used to clear the ALT_MON_GPIO_PORTA_EOI_CCD register field value. */
#define ALT_MON_GPIO_PORTA_EOI_CCD_CLR_MSK    0xffffffef
/* The reset value of the ALT_MON_GPIO_PORTA_EOI_CCD register field. */
#define ALT_MON_GPIO_PORTA_EOI_CCD_RESET      0x0
/* Extracts the ALT_MON_GPIO_PORTA_EOI_CCD field value from a register. */
#define ALT_MON_GPIO_PORTA_EOI_CCD_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_MON_GPIO_PORTA_EOI_CCD register field value suitable for setting the register. */
#define ALT_MON_GPIO_PORTA_EOI_CCD_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Clear Edge Interrupt Field (PR_READY) - prr
 * 
 * Used by software to clear an PR_READY edge interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description       
 * :-----------------------------------|:------|:-------------------
 *  ALT_MON_GPIO_PORTA_EOI_PRR_E_NOCLR | 0x0   | No interrupt clear
 *  ALT_MON_GPIO_PORTA_EOI_PRR_E_CLR   | 0x1   | Clear interrupt   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_PRR
 * 
 * No interrupt clear
 */
#define ALT_MON_GPIO_PORTA_EOI_PRR_E_NOCLR  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_PRR
 * 
 * Clear interrupt
 */
#define ALT_MON_GPIO_PORTA_EOI_PRR_E_CLR    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_PORTA_EOI_PRR register field. */
#define ALT_MON_GPIO_PORTA_EOI_PRR_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_PORTA_EOI_PRR register field. */
#define ALT_MON_GPIO_PORTA_EOI_PRR_MSB        5
/* The width in bits of the ALT_MON_GPIO_PORTA_EOI_PRR register field. */
#define ALT_MON_GPIO_PORTA_EOI_PRR_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_PORTA_EOI_PRR register field value. */
#define ALT_MON_GPIO_PORTA_EOI_PRR_SET_MSK    0x00000020
/* The mask used to clear the ALT_MON_GPIO_PORTA_EOI_PRR register field value. */
#define ALT_MON_GPIO_PORTA_EOI_PRR_CLR_MSK    0xffffffdf
/* The reset value of the ALT_MON_GPIO_PORTA_EOI_PRR register field. */
#define ALT_MON_GPIO_PORTA_EOI_PRR_RESET      0x0
/* Extracts the ALT_MON_GPIO_PORTA_EOI_PRR field value from a register. */
#define ALT_MON_GPIO_PORTA_EOI_PRR_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_MON_GPIO_PORTA_EOI_PRR register field value suitable for setting the register. */
#define ALT_MON_GPIO_PORTA_EOI_PRR_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Clear Edge Interrupt Field (PR_ERROR) - pre
 * 
 * Used by software to clear an PR_ERROR edge interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description       
 * :-----------------------------------|:------|:-------------------
 *  ALT_MON_GPIO_PORTA_EOI_PRE_E_NOCLR | 0x0   | No interrupt clear
 *  ALT_MON_GPIO_PORTA_EOI_PRE_E_CLR   | 0x1   | Clear interrupt   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_PRE
 * 
 * No interrupt clear
 */
#define ALT_MON_GPIO_PORTA_EOI_PRE_E_NOCLR  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_PRE
 * 
 * Clear interrupt
 */
#define ALT_MON_GPIO_PORTA_EOI_PRE_E_CLR    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_PORTA_EOI_PRE register field. */
#define ALT_MON_GPIO_PORTA_EOI_PRE_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_PORTA_EOI_PRE register field. */
#define ALT_MON_GPIO_PORTA_EOI_PRE_MSB        6
/* The width in bits of the ALT_MON_GPIO_PORTA_EOI_PRE register field. */
#define ALT_MON_GPIO_PORTA_EOI_PRE_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_PORTA_EOI_PRE register field value. */
#define ALT_MON_GPIO_PORTA_EOI_PRE_SET_MSK    0x00000040
/* The mask used to clear the ALT_MON_GPIO_PORTA_EOI_PRE register field value. */
#define ALT_MON_GPIO_PORTA_EOI_PRE_CLR_MSK    0xffffffbf
/* The reset value of the ALT_MON_GPIO_PORTA_EOI_PRE register field. */
#define ALT_MON_GPIO_PORTA_EOI_PRE_RESET      0x0
/* Extracts the ALT_MON_GPIO_PORTA_EOI_PRE field value from a register. */
#define ALT_MON_GPIO_PORTA_EOI_PRE_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_MON_GPIO_PORTA_EOI_PRE register field value suitable for setting the register. */
#define ALT_MON_GPIO_PORTA_EOI_PRE_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Clear Edge Interrupt Field (PR_DONE) - prd
 * 
 * Used by software to clear an PR_DONE edge interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description       
 * :-----------------------------------|:------|:-------------------
 *  ALT_MON_GPIO_PORTA_EOI_PRD_E_NOCLR | 0x0   | No interrupt clear
 *  ALT_MON_GPIO_PORTA_EOI_PRD_E_CLR   | 0x1   | Clear interrupt   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_PRD
 * 
 * No interrupt clear
 */
#define ALT_MON_GPIO_PORTA_EOI_PRD_E_NOCLR  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_PRD
 * 
 * Clear interrupt
 */
#define ALT_MON_GPIO_PORTA_EOI_PRD_E_CLR    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_PORTA_EOI_PRD register field. */
#define ALT_MON_GPIO_PORTA_EOI_PRD_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_PORTA_EOI_PRD register field. */
#define ALT_MON_GPIO_PORTA_EOI_PRD_MSB        7
/* The width in bits of the ALT_MON_GPIO_PORTA_EOI_PRD register field. */
#define ALT_MON_GPIO_PORTA_EOI_PRD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_PORTA_EOI_PRD register field value. */
#define ALT_MON_GPIO_PORTA_EOI_PRD_SET_MSK    0x00000080
/* The mask used to clear the ALT_MON_GPIO_PORTA_EOI_PRD register field value. */
#define ALT_MON_GPIO_PORTA_EOI_PRD_CLR_MSK    0xffffff7f
/* The reset value of the ALT_MON_GPIO_PORTA_EOI_PRD register field. */
#define ALT_MON_GPIO_PORTA_EOI_PRD_RESET      0x0
/* Extracts the ALT_MON_GPIO_PORTA_EOI_PRD field value from a register. */
#define ALT_MON_GPIO_PORTA_EOI_PRD_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_MON_GPIO_PORTA_EOI_PRD register field value suitable for setting the register. */
#define ALT_MON_GPIO_PORTA_EOI_PRD_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : Clear Edge Interrupt Field (nCONFIG Pin) - ncp
 * 
 * Used by software to clear an nCONFIG Pin edge interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description       
 * :-----------------------------------|:------|:-------------------
 *  ALT_MON_GPIO_PORTA_EOI_NCP_E_NOCLR | 0x0   | No interrupt clear
 *  ALT_MON_GPIO_PORTA_EOI_NCP_E_CLR   | 0x1   | Clear interrupt   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_NCP
 * 
 * No interrupt clear
 */
#define ALT_MON_GPIO_PORTA_EOI_NCP_E_NOCLR  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_NCP
 * 
 * Clear interrupt
 */
#define ALT_MON_GPIO_PORTA_EOI_NCP_E_CLR    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_PORTA_EOI_NCP register field. */
#define ALT_MON_GPIO_PORTA_EOI_NCP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_PORTA_EOI_NCP register field. */
#define ALT_MON_GPIO_PORTA_EOI_NCP_MSB        8
/* The width in bits of the ALT_MON_GPIO_PORTA_EOI_NCP register field. */
#define ALT_MON_GPIO_PORTA_EOI_NCP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_PORTA_EOI_NCP register field value. */
#define ALT_MON_GPIO_PORTA_EOI_NCP_SET_MSK    0x00000100
/* The mask used to clear the ALT_MON_GPIO_PORTA_EOI_NCP register field value. */
#define ALT_MON_GPIO_PORTA_EOI_NCP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_MON_GPIO_PORTA_EOI_NCP register field. */
#define ALT_MON_GPIO_PORTA_EOI_NCP_RESET      0x0
/* Extracts the ALT_MON_GPIO_PORTA_EOI_NCP field value from a register. */
#define ALT_MON_GPIO_PORTA_EOI_NCP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_MON_GPIO_PORTA_EOI_NCP register field value suitable for setting the register. */
#define ALT_MON_GPIO_PORTA_EOI_NCP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Clear Edge Interrupt Field (nSTATUS Pin) - nsp
 * 
 * Used by software to clear an nSTATUS Pin edge interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description       
 * :-----------------------------------|:------|:-------------------
 *  ALT_MON_GPIO_PORTA_EOI_NSP_E_NOCLR | 0x0   | No interrupt clear
 *  ALT_MON_GPIO_PORTA_EOI_NSP_E_CLR   | 0x1   | Clear interrupt   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_NSP
 * 
 * No interrupt clear
 */
#define ALT_MON_GPIO_PORTA_EOI_NSP_E_NOCLR  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_NSP
 * 
 * Clear interrupt
 */
#define ALT_MON_GPIO_PORTA_EOI_NSP_E_CLR    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_PORTA_EOI_NSP register field. */
#define ALT_MON_GPIO_PORTA_EOI_NSP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_PORTA_EOI_NSP register field. */
#define ALT_MON_GPIO_PORTA_EOI_NSP_MSB        9
/* The width in bits of the ALT_MON_GPIO_PORTA_EOI_NSP register field. */
#define ALT_MON_GPIO_PORTA_EOI_NSP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_PORTA_EOI_NSP register field value. */
#define ALT_MON_GPIO_PORTA_EOI_NSP_SET_MSK    0x00000200
/* The mask used to clear the ALT_MON_GPIO_PORTA_EOI_NSP register field value. */
#define ALT_MON_GPIO_PORTA_EOI_NSP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_MON_GPIO_PORTA_EOI_NSP register field. */
#define ALT_MON_GPIO_PORTA_EOI_NSP_RESET      0x0
/* Extracts the ALT_MON_GPIO_PORTA_EOI_NSP field value from a register. */
#define ALT_MON_GPIO_PORTA_EOI_NSP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_MON_GPIO_PORTA_EOI_NSP register field value suitable for setting the register. */
#define ALT_MON_GPIO_PORTA_EOI_NSP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : Clear Edge Interrupt Field (CONF_DONE Pin) - cdp
 * 
 * Used by software to clear an CONF_DONE Pin edge interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description       
 * :-----------------------------------|:------|:-------------------
 *  ALT_MON_GPIO_PORTA_EOI_CDP_E_NOCLR | 0x0   | No interrupt clear
 *  ALT_MON_GPIO_PORTA_EOI_CDP_E_CLR   | 0x1   | Clear interrupt   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_CDP
 * 
 * No interrupt clear
 */
#define ALT_MON_GPIO_PORTA_EOI_CDP_E_NOCLR  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_CDP
 * 
 * Clear interrupt
 */
#define ALT_MON_GPIO_PORTA_EOI_CDP_E_CLR    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_PORTA_EOI_CDP register field. */
#define ALT_MON_GPIO_PORTA_EOI_CDP_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_PORTA_EOI_CDP register field. */
#define ALT_MON_GPIO_PORTA_EOI_CDP_MSB        10
/* The width in bits of the ALT_MON_GPIO_PORTA_EOI_CDP register field. */
#define ALT_MON_GPIO_PORTA_EOI_CDP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_PORTA_EOI_CDP register field value. */
#define ALT_MON_GPIO_PORTA_EOI_CDP_SET_MSK    0x00000400
/* The mask used to clear the ALT_MON_GPIO_PORTA_EOI_CDP register field value. */
#define ALT_MON_GPIO_PORTA_EOI_CDP_CLR_MSK    0xfffffbff
/* The reset value of the ALT_MON_GPIO_PORTA_EOI_CDP register field. */
#define ALT_MON_GPIO_PORTA_EOI_CDP_RESET      0x0
/* Extracts the ALT_MON_GPIO_PORTA_EOI_CDP field value from a register. */
#define ALT_MON_GPIO_PORTA_EOI_CDP_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_MON_GPIO_PORTA_EOI_CDP register field value suitable for setting the register. */
#define ALT_MON_GPIO_PORTA_EOI_CDP_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : Clear Edge Interrupt Field (FPGA_POWER_ON) - fpo
 * 
 * Used by software to clear an FPGA_POWER_ON edge interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description       
 * :-----------------------------------|:------|:-------------------
 *  ALT_MON_GPIO_PORTA_EOI_FPO_E_NOCLR | 0x0   | No interrupt clear
 *  ALT_MON_GPIO_PORTA_EOI_FPO_E_CLR   | 0x1   | Clear interrupt   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_FPO
 * 
 * No interrupt clear
 */
#define ALT_MON_GPIO_PORTA_EOI_FPO_E_NOCLR  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_PORTA_EOI_FPO
 * 
 * Clear interrupt
 */
#define ALT_MON_GPIO_PORTA_EOI_FPO_E_CLR    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_PORTA_EOI_FPO register field. */
#define ALT_MON_GPIO_PORTA_EOI_FPO_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_PORTA_EOI_FPO register field. */
#define ALT_MON_GPIO_PORTA_EOI_FPO_MSB        11
/* The width in bits of the ALT_MON_GPIO_PORTA_EOI_FPO register field. */
#define ALT_MON_GPIO_PORTA_EOI_FPO_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_PORTA_EOI_FPO register field value. */
#define ALT_MON_GPIO_PORTA_EOI_FPO_SET_MSK    0x00000800
/* The mask used to clear the ALT_MON_GPIO_PORTA_EOI_FPO register field value. */
#define ALT_MON_GPIO_PORTA_EOI_FPO_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_MON_GPIO_PORTA_EOI_FPO register field. */
#define ALT_MON_GPIO_PORTA_EOI_FPO_RESET      0x0
/* Extracts the ALT_MON_GPIO_PORTA_EOI_FPO field value from a register. */
#define ALT_MON_GPIO_PORTA_EOI_FPO_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_MON_GPIO_PORTA_EOI_FPO register field value suitable for setting the register. */
#define ALT_MON_GPIO_PORTA_EOI_FPO_SET(value) (((value) << 11) & 0x00000800)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_MON_GPIO_PORTA_EOI.
 */
struct ALT_MON_GPIO_PORTA_EOI_s
{
    uint32_t  ns  :  1;  /* Clear Edge Interrupt Field (nSTATUS) */
    uint32_t  cd  :  1;  /* Clear Edge Interrupt Field (CONF_DONE) */
    uint32_t  id  :  1;  /* Clear Edge Interrupt Field (INIT_DONE) */
    uint32_t  crc :  1;  /* Clear Edge Interrupt Field (CRC_ERROR) */
    uint32_t  ccd :  1;  /* Clear Edge Interrupt Field (CVP_CONF_DONE) */
    uint32_t  prr :  1;  /* Clear Edge Interrupt Field (PR_READY) */
    uint32_t  pre :  1;  /* Clear Edge Interrupt Field (PR_ERROR) */
    uint32_t  prd :  1;  /* Clear Edge Interrupt Field (PR_DONE) */
    uint32_t  ncp :  1;  /* Clear Edge Interrupt Field (nCONFIG Pin) */
    uint32_t  nsp :  1;  /* Clear Edge Interrupt Field (nSTATUS Pin) */
    uint32_t  cdp :  1;  /* Clear Edge Interrupt Field (CONF_DONE Pin) */
    uint32_t  fpo :  1;  /* Clear Edge Interrupt Field (FPGA_POWER_ON) */
    uint32_t      : 20;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_MON_GPIO_PORTA_EOI. */
typedef volatile struct ALT_MON_GPIO_PORTA_EOI_s  ALT_MON_GPIO_PORTA_EOI_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_MON_GPIO_PORTA_EOI register from the beginning of the component. */
#define ALT_MON_GPIO_PORTA_EOI_OFST        0x4c
/* The address of the ALT_MON_GPIO_PORTA_EOI register. */
#define ALT_MON_GPIO_PORTA_EOI_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_MON_GPIO_PORTA_EOI_OFST))

/*
 * Register : External Port A Register - gpio_ext_porta
 * 
 * Reading this register reads the values of the GPIO inputs.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                        
 * :--------|:-------|:------|:------------------------------------
 *  [0]     | R      | 0x0   | External Port Field (nSTATUS)      
 *  [1]     | R      | 0x0   | External Port Field (CONF_DONE)    
 *  [2]     | R      | 0x0   | External Port Field (INIT_DONE)    
 *  [3]     | R      | 0x0   | External Port Field (CRC_ERROR)    
 *  [4]     | R      | 0x0   | External Port Field (CVP_CONF_DONE)
 *  [5]     | R      | 0x0   | External Port Field (PR_READY)     
 *  [6]     | R      | 0x0   | External Port Field (PR_ERROR)     
 *  [7]     | R      | 0x0   | External Port Field (PR_DONE)      
 *  [8]     | R      | 0x0   | External Port Field (nCONFIG Pin)  
 *  [9]     | R      | 0x0   | External Port Field (nSTATUS Pin)  
 *  [10]    | R      | 0x0   | External Port Field (CONF_DONE Pin)
 *  [11]    | R      | 0x0   | External Port Field (FPGA_POWER_ON)
 *  [31:12] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : External Port Field (nSTATUS) - ns
 * 
 * Reading this provides the value of nSTATUS
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_EXT_PORTA_NS register field. */
#define ALT_MON_GPIO_EXT_PORTA_NS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_EXT_PORTA_NS register field. */
#define ALT_MON_GPIO_EXT_PORTA_NS_MSB        0
/* The width in bits of the ALT_MON_GPIO_EXT_PORTA_NS register field. */
#define ALT_MON_GPIO_EXT_PORTA_NS_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_EXT_PORTA_NS register field value. */
#define ALT_MON_GPIO_EXT_PORTA_NS_SET_MSK    0x00000001
/* The mask used to clear the ALT_MON_GPIO_EXT_PORTA_NS register field value. */
#define ALT_MON_GPIO_EXT_PORTA_NS_CLR_MSK    0xfffffffe
/* The reset value of the ALT_MON_GPIO_EXT_PORTA_NS register field. */
#define ALT_MON_GPIO_EXT_PORTA_NS_RESET      0x0
/* Extracts the ALT_MON_GPIO_EXT_PORTA_NS field value from a register. */
#define ALT_MON_GPIO_EXT_PORTA_NS_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_MON_GPIO_EXT_PORTA_NS register field value suitable for setting the register. */
#define ALT_MON_GPIO_EXT_PORTA_NS_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : External Port Field (CONF_DONE) - cd
 * 
 * Reading this provides the value of CONF_DONE
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_EXT_PORTA_CD register field. */
#define ALT_MON_GPIO_EXT_PORTA_CD_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_EXT_PORTA_CD register field. */
#define ALT_MON_GPIO_EXT_PORTA_CD_MSB        1
/* The width in bits of the ALT_MON_GPIO_EXT_PORTA_CD register field. */
#define ALT_MON_GPIO_EXT_PORTA_CD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_EXT_PORTA_CD register field value. */
#define ALT_MON_GPIO_EXT_PORTA_CD_SET_MSK    0x00000002
/* The mask used to clear the ALT_MON_GPIO_EXT_PORTA_CD register field value. */
#define ALT_MON_GPIO_EXT_PORTA_CD_CLR_MSK    0xfffffffd
/* The reset value of the ALT_MON_GPIO_EXT_PORTA_CD register field. */
#define ALT_MON_GPIO_EXT_PORTA_CD_RESET      0x0
/* Extracts the ALT_MON_GPIO_EXT_PORTA_CD field value from a register. */
#define ALT_MON_GPIO_EXT_PORTA_CD_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_MON_GPIO_EXT_PORTA_CD register field value suitable for setting the register. */
#define ALT_MON_GPIO_EXT_PORTA_CD_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : External Port Field (INIT_DONE) - id
 * 
 * Reading this provides the value of INIT_DONE
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_EXT_PORTA_ID register field. */
#define ALT_MON_GPIO_EXT_PORTA_ID_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_EXT_PORTA_ID register field. */
#define ALT_MON_GPIO_EXT_PORTA_ID_MSB        2
/* The width in bits of the ALT_MON_GPIO_EXT_PORTA_ID register field. */
#define ALT_MON_GPIO_EXT_PORTA_ID_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_EXT_PORTA_ID register field value. */
#define ALT_MON_GPIO_EXT_PORTA_ID_SET_MSK    0x00000004
/* The mask used to clear the ALT_MON_GPIO_EXT_PORTA_ID register field value. */
#define ALT_MON_GPIO_EXT_PORTA_ID_CLR_MSK    0xfffffffb
/* The reset value of the ALT_MON_GPIO_EXT_PORTA_ID register field. */
#define ALT_MON_GPIO_EXT_PORTA_ID_RESET      0x0
/* Extracts the ALT_MON_GPIO_EXT_PORTA_ID field value from a register. */
#define ALT_MON_GPIO_EXT_PORTA_ID_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_MON_GPIO_EXT_PORTA_ID register field value suitable for setting the register. */
#define ALT_MON_GPIO_EXT_PORTA_ID_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : External Port Field (CRC_ERROR) - crc
 * 
 * Reading this provides the value of CRC_ERROR
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_EXT_PORTA_CRC register field. */
#define ALT_MON_GPIO_EXT_PORTA_CRC_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_EXT_PORTA_CRC register field. */
#define ALT_MON_GPIO_EXT_PORTA_CRC_MSB        3
/* The width in bits of the ALT_MON_GPIO_EXT_PORTA_CRC register field. */
#define ALT_MON_GPIO_EXT_PORTA_CRC_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_EXT_PORTA_CRC register field value. */
#define ALT_MON_GPIO_EXT_PORTA_CRC_SET_MSK    0x00000008
/* The mask used to clear the ALT_MON_GPIO_EXT_PORTA_CRC register field value. */
#define ALT_MON_GPIO_EXT_PORTA_CRC_CLR_MSK    0xfffffff7
/* The reset value of the ALT_MON_GPIO_EXT_PORTA_CRC register field. */
#define ALT_MON_GPIO_EXT_PORTA_CRC_RESET      0x0
/* Extracts the ALT_MON_GPIO_EXT_PORTA_CRC field value from a register. */
#define ALT_MON_GPIO_EXT_PORTA_CRC_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_MON_GPIO_EXT_PORTA_CRC register field value suitable for setting the register. */
#define ALT_MON_GPIO_EXT_PORTA_CRC_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : External Port Field (CVP_CONF_DONE) - ccd
 * 
 * Reading this provides the value of CVP_CONF_DONE
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_EXT_PORTA_CCD register field. */
#define ALT_MON_GPIO_EXT_PORTA_CCD_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_EXT_PORTA_CCD register field. */
#define ALT_MON_GPIO_EXT_PORTA_CCD_MSB        4
/* The width in bits of the ALT_MON_GPIO_EXT_PORTA_CCD register field. */
#define ALT_MON_GPIO_EXT_PORTA_CCD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_EXT_PORTA_CCD register field value. */
#define ALT_MON_GPIO_EXT_PORTA_CCD_SET_MSK    0x00000010
/* The mask used to clear the ALT_MON_GPIO_EXT_PORTA_CCD register field value. */
#define ALT_MON_GPIO_EXT_PORTA_CCD_CLR_MSK    0xffffffef
/* The reset value of the ALT_MON_GPIO_EXT_PORTA_CCD register field. */
#define ALT_MON_GPIO_EXT_PORTA_CCD_RESET      0x0
/* Extracts the ALT_MON_GPIO_EXT_PORTA_CCD field value from a register. */
#define ALT_MON_GPIO_EXT_PORTA_CCD_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_MON_GPIO_EXT_PORTA_CCD register field value suitable for setting the register. */
#define ALT_MON_GPIO_EXT_PORTA_CCD_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : External Port Field (PR_READY) - prr
 * 
 * Reading this provides the value of PR_READY
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_EXT_PORTA_PRR register field. */
#define ALT_MON_GPIO_EXT_PORTA_PRR_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_EXT_PORTA_PRR register field. */
#define ALT_MON_GPIO_EXT_PORTA_PRR_MSB        5
/* The width in bits of the ALT_MON_GPIO_EXT_PORTA_PRR register field. */
#define ALT_MON_GPIO_EXT_PORTA_PRR_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_EXT_PORTA_PRR register field value. */
#define ALT_MON_GPIO_EXT_PORTA_PRR_SET_MSK    0x00000020
/* The mask used to clear the ALT_MON_GPIO_EXT_PORTA_PRR register field value. */
#define ALT_MON_GPIO_EXT_PORTA_PRR_CLR_MSK    0xffffffdf
/* The reset value of the ALT_MON_GPIO_EXT_PORTA_PRR register field. */
#define ALT_MON_GPIO_EXT_PORTA_PRR_RESET      0x0
/* Extracts the ALT_MON_GPIO_EXT_PORTA_PRR field value from a register. */
#define ALT_MON_GPIO_EXT_PORTA_PRR_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_MON_GPIO_EXT_PORTA_PRR register field value suitable for setting the register. */
#define ALT_MON_GPIO_EXT_PORTA_PRR_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : External Port Field (PR_ERROR) - pre
 * 
 * Reading this provides the value of PR_ERROR
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_EXT_PORTA_PRE register field. */
#define ALT_MON_GPIO_EXT_PORTA_PRE_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_EXT_PORTA_PRE register field. */
#define ALT_MON_GPIO_EXT_PORTA_PRE_MSB        6
/* The width in bits of the ALT_MON_GPIO_EXT_PORTA_PRE register field. */
#define ALT_MON_GPIO_EXT_PORTA_PRE_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_EXT_PORTA_PRE register field value. */
#define ALT_MON_GPIO_EXT_PORTA_PRE_SET_MSK    0x00000040
/* The mask used to clear the ALT_MON_GPIO_EXT_PORTA_PRE register field value. */
#define ALT_MON_GPIO_EXT_PORTA_PRE_CLR_MSK    0xffffffbf
/* The reset value of the ALT_MON_GPIO_EXT_PORTA_PRE register field. */
#define ALT_MON_GPIO_EXT_PORTA_PRE_RESET      0x0
/* Extracts the ALT_MON_GPIO_EXT_PORTA_PRE field value from a register. */
#define ALT_MON_GPIO_EXT_PORTA_PRE_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_MON_GPIO_EXT_PORTA_PRE register field value suitable for setting the register. */
#define ALT_MON_GPIO_EXT_PORTA_PRE_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : External Port Field (PR_DONE) - prd
 * 
 * Reading this provides the value of PR_DONE
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_EXT_PORTA_PRD register field. */
#define ALT_MON_GPIO_EXT_PORTA_PRD_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_EXT_PORTA_PRD register field. */
#define ALT_MON_GPIO_EXT_PORTA_PRD_MSB        7
/* The width in bits of the ALT_MON_GPIO_EXT_PORTA_PRD register field. */
#define ALT_MON_GPIO_EXT_PORTA_PRD_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_EXT_PORTA_PRD register field value. */
#define ALT_MON_GPIO_EXT_PORTA_PRD_SET_MSK    0x00000080
/* The mask used to clear the ALT_MON_GPIO_EXT_PORTA_PRD register field value. */
#define ALT_MON_GPIO_EXT_PORTA_PRD_CLR_MSK    0xffffff7f
/* The reset value of the ALT_MON_GPIO_EXT_PORTA_PRD register field. */
#define ALT_MON_GPIO_EXT_PORTA_PRD_RESET      0x0
/* Extracts the ALT_MON_GPIO_EXT_PORTA_PRD field value from a register. */
#define ALT_MON_GPIO_EXT_PORTA_PRD_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_MON_GPIO_EXT_PORTA_PRD register field value suitable for setting the register. */
#define ALT_MON_GPIO_EXT_PORTA_PRD_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : External Port Field (nCONFIG Pin) - ncp
 * 
 * Reading this provides the value of nCONFIG Pin
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_EXT_PORTA_NCP register field. */
#define ALT_MON_GPIO_EXT_PORTA_NCP_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_EXT_PORTA_NCP register field. */
#define ALT_MON_GPIO_EXT_PORTA_NCP_MSB        8
/* The width in bits of the ALT_MON_GPIO_EXT_PORTA_NCP register field. */
#define ALT_MON_GPIO_EXT_PORTA_NCP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_EXT_PORTA_NCP register field value. */
#define ALT_MON_GPIO_EXT_PORTA_NCP_SET_MSK    0x00000100
/* The mask used to clear the ALT_MON_GPIO_EXT_PORTA_NCP register field value. */
#define ALT_MON_GPIO_EXT_PORTA_NCP_CLR_MSK    0xfffffeff
/* The reset value of the ALT_MON_GPIO_EXT_PORTA_NCP register field. */
#define ALT_MON_GPIO_EXT_PORTA_NCP_RESET      0x0
/* Extracts the ALT_MON_GPIO_EXT_PORTA_NCP field value from a register. */
#define ALT_MON_GPIO_EXT_PORTA_NCP_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_MON_GPIO_EXT_PORTA_NCP register field value suitable for setting the register. */
#define ALT_MON_GPIO_EXT_PORTA_NCP_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : External Port Field (nSTATUS Pin) - nsp
 * 
 * Reading this provides the value of nSTATUS Pin
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_EXT_PORTA_NSP register field. */
#define ALT_MON_GPIO_EXT_PORTA_NSP_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_EXT_PORTA_NSP register field. */
#define ALT_MON_GPIO_EXT_PORTA_NSP_MSB        9
/* The width in bits of the ALT_MON_GPIO_EXT_PORTA_NSP register field. */
#define ALT_MON_GPIO_EXT_PORTA_NSP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_EXT_PORTA_NSP register field value. */
#define ALT_MON_GPIO_EXT_PORTA_NSP_SET_MSK    0x00000200
/* The mask used to clear the ALT_MON_GPIO_EXT_PORTA_NSP register field value. */
#define ALT_MON_GPIO_EXT_PORTA_NSP_CLR_MSK    0xfffffdff
/* The reset value of the ALT_MON_GPIO_EXT_PORTA_NSP register field. */
#define ALT_MON_GPIO_EXT_PORTA_NSP_RESET      0x0
/* Extracts the ALT_MON_GPIO_EXT_PORTA_NSP field value from a register. */
#define ALT_MON_GPIO_EXT_PORTA_NSP_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_MON_GPIO_EXT_PORTA_NSP register field value suitable for setting the register. */
#define ALT_MON_GPIO_EXT_PORTA_NSP_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : External Port Field (CONF_DONE Pin) - cdp
 * 
 * Reading this provides the value of CONF_DONE Pin
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_EXT_PORTA_CDP register field. */
#define ALT_MON_GPIO_EXT_PORTA_CDP_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_EXT_PORTA_CDP register field. */
#define ALT_MON_GPIO_EXT_PORTA_CDP_MSB        10
/* The width in bits of the ALT_MON_GPIO_EXT_PORTA_CDP register field. */
#define ALT_MON_GPIO_EXT_PORTA_CDP_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_EXT_PORTA_CDP register field value. */
#define ALT_MON_GPIO_EXT_PORTA_CDP_SET_MSK    0x00000400
/* The mask used to clear the ALT_MON_GPIO_EXT_PORTA_CDP register field value. */
#define ALT_MON_GPIO_EXT_PORTA_CDP_CLR_MSK    0xfffffbff
/* The reset value of the ALT_MON_GPIO_EXT_PORTA_CDP register field. */
#define ALT_MON_GPIO_EXT_PORTA_CDP_RESET      0x0
/* Extracts the ALT_MON_GPIO_EXT_PORTA_CDP field value from a register. */
#define ALT_MON_GPIO_EXT_PORTA_CDP_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_MON_GPIO_EXT_PORTA_CDP register field value suitable for setting the register. */
#define ALT_MON_GPIO_EXT_PORTA_CDP_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : External Port Field (FPGA_POWER_ON) - fpo
 * 
 * Reading this provides the value of FPGA_POWER_ON
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_EXT_PORTA_FPO register field. */
#define ALT_MON_GPIO_EXT_PORTA_FPO_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_EXT_PORTA_FPO register field. */
#define ALT_MON_GPIO_EXT_PORTA_FPO_MSB        11
/* The width in bits of the ALT_MON_GPIO_EXT_PORTA_FPO register field. */
#define ALT_MON_GPIO_EXT_PORTA_FPO_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_EXT_PORTA_FPO register field value. */
#define ALT_MON_GPIO_EXT_PORTA_FPO_SET_MSK    0x00000800
/* The mask used to clear the ALT_MON_GPIO_EXT_PORTA_FPO register field value. */
#define ALT_MON_GPIO_EXT_PORTA_FPO_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_MON_GPIO_EXT_PORTA_FPO register field. */
#define ALT_MON_GPIO_EXT_PORTA_FPO_RESET      0x0
/* Extracts the ALT_MON_GPIO_EXT_PORTA_FPO field value from a register. */
#define ALT_MON_GPIO_EXT_PORTA_FPO_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_MON_GPIO_EXT_PORTA_FPO register field value suitable for setting the register. */
#define ALT_MON_GPIO_EXT_PORTA_FPO_SET(value) (((value) << 11) & 0x00000800)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_MON_GPIO_EXT_PORTA.
 */
struct ALT_MON_GPIO_EXT_PORTA_s
{
    const uint32_t  ns  :  1;  /* External Port Field (nSTATUS) */
    const uint32_t  cd  :  1;  /* External Port Field (CONF_DONE) */
    const uint32_t  id  :  1;  /* External Port Field (INIT_DONE) */
    const uint32_t  crc :  1;  /* External Port Field (CRC_ERROR) */
    const uint32_t  ccd :  1;  /* External Port Field (CVP_CONF_DONE) */
    const uint32_t  prr :  1;  /* External Port Field (PR_READY) */
    const uint32_t  pre :  1;  /* External Port Field (PR_ERROR) */
    const uint32_t  prd :  1;  /* External Port Field (PR_DONE) */
    const uint32_t  ncp :  1;  /* External Port Field (nCONFIG Pin) */
    const uint32_t  nsp :  1;  /* External Port Field (nSTATUS Pin) */
    const uint32_t  cdp :  1;  /* External Port Field (CONF_DONE Pin) */
    const uint32_t  fpo :  1;  /* External Port Field (FPGA_POWER_ON) */
    uint32_t            : 20;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_MON_GPIO_EXT_PORTA. */
typedef volatile struct ALT_MON_GPIO_EXT_PORTA_s  ALT_MON_GPIO_EXT_PORTA_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_MON_GPIO_EXT_PORTA register from the beginning of the component. */
#define ALT_MON_GPIO_EXT_PORTA_OFST        0x50
/* The address of the ALT_MON_GPIO_EXT_PORTA register. */
#define ALT_MON_GPIO_EXT_PORTA_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_MON_GPIO_EXT_PORTA_OFST))

/*
 * Register : Synchronization Level Register - gpio_ls_sync
 * 
 * The Synchronization level register is used to synchronize inputs to the
 * l4_mp_clk. All MON interrupts are already synchronized before the GPIO instance
 * so it is not necessary to setup this register to enable synchronization.
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
 *  Enum                                       | Value | Description                    
 * :-------------------------------------------|:------|:--------------------------------
 *  ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC_E_NOSYNC | 0x0   | No synchronization to l4_mp_clk
 *  ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC_E_SYNC   | 0x1   | Synchronize to l4_mp_clk       
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC
 * 
 * No synchronization to l4_mp_clk
 */
#define ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC_E_NOSYNC  0x0
/*
 * Enumerated value for register field ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC
 * 
 * Synchronize to l4_mp_clk
 */
#define ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC_E_SYNC    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC register field. */
#define ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC register field. */
#define ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC_MSB        0
/* The width in bits of the ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC register field. */
#define ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC register field value. */
#define ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC_SET_MSK    0x00000001
/* The mask used to clear the ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC register field value. */
#define ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC_CLR_MSK    0xfffffffe
/* The reset value of the ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC register field. */
#define ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC_RESET      0x0
/* Extracts the ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC field value from a register. */
#define ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC register field value suitable for setting the register. */
#define ALT_MON_GPIO_LS_SYNC_GPIO_LS_SYNC_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_MON_GPIO_LS_SYNC.
 */
struct ALT_MON_GPIO_LS_SYNC_s
{
    uint32_t  gpio_ls_sync :  1;  /* Synchronization Level Field */
    uint32_t               : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_MON_GPIO_LS_SYNC. */
typedef volatile struct ALT_MON_GPIO_LS_SYNC_s  ALT_MON_GPIO_LS_SYNC_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_MON_GPIO_LS_SYNC register from the beginning of the component. */
#define ALT_MON_GPIO_LS_SYNC_OFST        0x60
/* The address of the ALT_MON_GPIO_LS_SYNC register. */
#define ALT_MON_GPIO_LS_SYNC_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_MON_GPIO_LS_SYNC_OFST))

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
/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE register field. */
#define ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE register field. */
#define ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_MSB        31
/* The width in bits of the ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE register field. */
#define ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_WIDTH      32
/* The mask used to set the ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE register field value. */
#define ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_SET_MSK    0xffffffff
/* The mask used to clear the ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE register field value. */
#define ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_CLR_MSK    0x00000000
/* The reset value of the ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE register field. */
#define ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_RESET      0x3230382a
/* Extracts the ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE field value from a register. */
#define ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE register field value suitable for setting the register. */
#define ALT_MON_GPIO_VER_ID_CODE_GPIO_VER_ID_CODE_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_MON_GPIO_VER_ID_CODE.
 */
struct ALT_MON_GPIO_VER_ID_CODE_s
{
    const uint32_t  gpio_ver_id_code : 32;  /* ASCII Component Version Field */
};

/* The typedef declaration for register ALT_MON_GPIO_VER_ID_CODE. */
typedef volatile struct ALT_MON_GPIO_VER_ID_CODE_s  ALT_MON_GPIO_VER_ID_CODE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_MON_GPIO_VER_ID_CODE register from the beginning of the component. */
#define ALT_MON_GPIO_VER_ID_CODE_OFST        0x6c
/* The address of the ALT_MON_GPIO_VER_ID_CODE register. */
#define ALT_MON_GPIO_VER_ID_CODE_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_MON_GPIO_VER_ID_CODE_OFST))

/*
 * Register : Configuration Register 2 - gpio_config_reg2
 * 
 * Specifies the bit width of port A.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description          
 * :--------|:-------|:------|:----------------------
 *  [4:0]   | R      | 0xb   | Port A Width (less 1)
 *  [9:5]   | R      | 0x7   | Port B Width (less 1)
 *  [14:10] | R      | 0x7   | Port C Width (less 1)
 *  [19:15] | R      | 0x7   | Port D Width (less 1)
 *  [31:20] | ???    | 0x0   | *UNDEFINED*          
 * 
 */
/*
 * Field : Port A Width (less 1) - encoded_id_pwidth_a
 * 
 * Specifies the width of GPIO Port A. The value 11 represents the 12-bit width
 * less one.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                       | Value | Description              
 * :-----------------------------------------------------------|:------|:--------------------------
 *  ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_E_WIDTHLESSONE8BITS  | 0x7   | Width (less 1) of 8 bits 
 *  ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_E_WIDTHLESSONE12BITS | 0xb   | Width (less 1) of 12 bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A
 * 
 * Width (less 1) of 8 bits
 */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_E_WIDTHLESSONE8BITS   0x7
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A
 * 
 * Width (less 1) of 12 bits
 */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_E_WIDTHLESSONE12BITS  0xb

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_MSB        4
/* The width in bits of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_WIDTH      5
/* The mask used to set the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A register field value. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_SET_MSK    0x0000001f
/* The mask used to clear the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A register field value. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_CLR_MSK    0xffffffe0
/* The reset value of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_RESET      0xb
/* Extracts the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A field value from a register. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_GET(value) (((value) & 0x0000001f) >> 0)
/* Produces a ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_A_SET(value) (((value) << 0) & 0x0000001f)

/*
 * Field : Port B Width (less 1) - encoded_id_pwidth_b
 * 
 * Specifies the width of GPIO Port B. Ignored because there is no Port B in the
 * GPIO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                       | Value | Description              
 * :-----------------------------------------------------------|:------|:--------------------------
 *  ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_E_WIDTHLESSONE8BITS  | 0x7   | Width (less 1) of 8 bits 
 *  ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_E_WIDTHLESSONE12BITS | 0xb   | Width (less 1) of 12 bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B
 * 
 * Width (less 1) of 8 bits
 */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_E_WIDTHLESSONE8BITS   0x7
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B
 * 
 * Width (less 1) of 12 bits
 */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_E_WIDTHLESSONE12BITS  0xb

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_MSB        9
/* The width in bits of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_WIDTH      5
/* The mask used to set the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B register field value. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_SET_MSK    0x000003e0
/* The mask used to clear the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B register field value. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_CLR_MSK    0xfffffc1f
/* The reset value of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_RESET      0x7
/* Extracts the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B field value from a register. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_GET(value) (((value) & 0x000003e0) >> 5)
/* Produces a ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_B_SET(value) (((value) << 5) & 0x000003e0)

/*
 * Field : Port C Width (less 1) - encoded_id_pwidth_c
 * 
 * Specifies the width of GPIO Port C. Ignored because there is no Port C in the
 * GPIO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                       | Value | Description              
 * :-----------------------------------------------------------|:------|:--------------------------
 *  ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_E_WIDTHLESSONE8BITS  | 0x7   | Width (less 1) of 8 bits 
 *  ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_E_WIDTHLESSONE12BITS | 0xb   | Width (less 1) of 12 bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C
 * 
 * Width (less 1) of 8 bits
 */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_E_WIDTHLESSONE8BITS   0x7
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C
 * 
 * Width (less 1) of 12 bits
 */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_E_WIDTHLESSONE12BITS  0xb

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_MSB        14
/* The width in bits of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_WIDTH      5
/* The mask used to set the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C register field value. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_SET_MSK    0x00007c00
/* The mask used to clear the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C register field value. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_CLR_MSK    0xffff83ff
/* The reset value of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_RESET      0x7
/* Extracts the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C field value from a register. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_GET(value) (((value) & 0x00007c00) >> 10)
/* Produces a ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_C_SET(value) (((value) << 10) & 0x00007c00)

/*
 * Field : Port D Width (less 1) - encoded_id_pwidth_d
 * 
 * Specifies the width of GPIO Port D. Ignored because there is no Port D in the
 * GPIO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                       | Value | Description              
 * :-----------------------------------------------------------|:------|:--------------------------
 *  ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_E_WIDTHLESSONE8BITS  | 0x7   | Width (less 1) of 8 bits 
 *  ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_E_WIDTHLESSONE12BITS | 0xb   | Width (less 1) of 12 bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D
 * 
 * Width (less 1) of 8 bits
 */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_E_WIDTHLESSONE8BITS   0x7
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D
 * 
 * Width (less 1) of 12 bits
 */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_E_WIDTHLESSONE12BITS  0xb

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_MSB        19
/* The width in bits of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_WIDTH      5
/* The mask used to set the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D register field value. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_SET_MSK    0x000f8000
/* The mask used to clear the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D register field value. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_CLR_MSK    0xfff07fff
/* The reset value of the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D register field. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_RESET      0x7
/* Extracts the ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D field value from a register. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_GET(value) (((value) & 0x000f8000) >> 15)
/* Produces a ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG2_ENC_ID_PWIDTH_D_SET(value) (((value) << 15) & 0x000f8000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_MON_GPIO_CFG_REG2.
 */
struct ALT_MON_GPIO_CFG_REG2_s
{
    const uint32_t  encoded_id_pwidth_a :  5;  /* Port A Width (less 1) */
    const uint32_t  encoded_id_pwidth_b :  5;  /* Port B Width (less 1) */
    const uint32_t  encoded_id_pwidth_c :  5;  /* Port C Width (less 1) */
    const uint32_t  encoded_id_pwidth_d :  5;  /* Port D Width (less 1) */
    uint32_t                            : 12;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_MON_GPIO_CFG_REG2. */
typedef volatile struct ALT_MON_GPIO_CFG_REG2_s  ALT_MON_GPIO_CFG_REG2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_MON_GPIO_CFG_REG2 register from the beginning of the component. */
#define ALT_MON_GPIO_CFG_REG2_OFST        0x70
/* The address of the ALT_MON_GPIO_CFG_REG2 register. */
#define ALT_MON_GPIO_CFG_REG2_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_MON_GPIO_CFG_REG2_OFST))

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
 *  [13]    | R      | 0x0   | Debounce Field                   
 *  [14]    | R      | 0x1   | Encoded GPIO Parameters Available
 *  [15]    | R      | 0x0   | ID Field                         
 *  [20:16] | R      | 0x1f  | Encoded ID Width Field           
 *  [31:21] | ???    | 0x0   | *UNDEFINED*                      
 * 
 */
/*
 * Field : APB DATA WIDTH - apb_data_width
 * 
 * Fixed to support an APB data bus width of 32-bits.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                               | Value | Description             
 * :---------------------------------------------------|:------|:-------------------------
 *  ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH_E_WIDTH32BITS | 0x2   | APB Data Width = 32-bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH
 * 
 * APB Data Width = 32-bits
 */
#define ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH_E_WIDTH32BITS  0x2

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH register field. */
#define ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH register field. */
#define ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH_MSB        1
/* The width in bits of the ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH register field. */
#define ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH_WIDTH      2
/* The mask used to set the ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH register field value. */
#define ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH_SET_MSK    0x00000003
/* The mask used to clear the ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH register field value. */
#define ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH_CLR_MSK    0xfffffffc
/* The reset value of the ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH register field. */
#define ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH_RESET      0x2
/* Extracts the ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH field value from a register. */
#define ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG1_APB_DATA_WIDTH_SET(value) (((value) << 0) & 0x00000003)

/*
 * Field : NUM PORTS - num_ports
 * 
 * The value of this register is fixed at one port (Port A).
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                       | Value | Description             
 * :-------------------------------------------|:------|:-------------------------
 *  ALT_MON_GPIO_CFG_REG1_NUM_PORTS_E_ONEPORTA | 0x0   | Number of GPIO Ports = 1
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG1_NUM_PORTS
 * 
 * Number of GPIO Ports = 1
 */
#define ALT_MON_GPIO_CFG_REG1_NUM_PORTS_E_ONEPORTA  0x0

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG1_NUM_PORTS register field. */
#define ALT_MON_GPIO_CFG_REG1_NUM_PORTS_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG1_NUM_PORTS register field. */
#define ALT_MON_GPIO_CFG_REG1_NUM_PORTS_MSB        3
/* The width in bits of the ALT_MON_GPIO_CFG_REG1_NUM_PORTS register field. */
#define ALT_MON_GPIO_CFG_REG1_NUM_PORTS_WIDTH      2
/* The mask used to set the ALT_MON_GPIO_CFG_REG1_NUM_PORTS register field value. */
#define ALT_MON_GPIO_CFG_REG1_NUM_PORTS_SET_MSK    0x0000000c
/* The mask used to clear the ALT_MON_GPIO_CFG_REG1_NUM_PORTS register field value. */
#define ALT_MON_GPIO_CFG_REG1_NUM_PORTS_CLR_MSK    0xfffffff3
/* The reset value of the ALT_MON_GPIO_CFG_REG1_NUM_PORTS register field. */
#define ALT_MON_GPIO_CFG_REG1_NUM_PORTS_RESET      0x0
/* Extracts the ALT_MON_GPIO_CFG_REG1_NUM_PORTS field value from a register. */
#define ALT_MON_GPIO_CFG_REG1_NUM_PORTS_GET(value) (((value) & 0x0000000c) >> 2)
/* Produces a ALT_MON_GPIO_CFG_REG1_NUM_PORTS register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG1_NUM_PORTS_SET(value) (((value) << 2) & 0x0000000c)

/*
 * Field : PORT A SINGLE CTL - porta_single_ctl
 * 
 * Indicates the mode of operation of Port A to be software controlled only.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                 | Value | Description                             
 * :-----------------------------------------------------|:------|:-----------------------------------------
 *  ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL_E_SOFTCTLONLY | 0x1   | Software Enabled Individual Port Control
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL
 * 
 * Software Enabled Individual Port Control
 */
#define ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL_E_SOFTCTLONLY    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL_MSB        4
/* The width in bits of the ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL register field value. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL_SET_MSK    0x00000010
/* The mask used to clear the ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL register field value. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL_CLR_MSK    0xffffffef
/* The reset value of the ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL_RESET      0x1
/* Extracts the ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL field value from a register. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_SINGLE_CTL_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : PORT B SINGLE CTL - portb_single_ctl
 * 
 * Indicates the mode of operation of Port B to be software controlled only.
 * Ignored because there is no Port B in the GPIO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                 | Value | Description                             
 * :-----------------------------------------------------|:------|:-----------------------------------------
 *  ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL_E_SOFTCTLONLY | 0x1   | Software Enabled Individual Port Control
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL
 * 
 * Software Enabled Individual Port Control
 */
#define ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL_E_SOFTCTLONLY    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL_MSB        5
/* The width in bits of the ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL register field value. */
#define ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL_SET_MSK    0x00000020
/* The mask used to clear the ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL register field value. */
#define ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL_CLR_MSK    0xffffffdf
/* The reset value of the ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL_RESET      0x1
/* Extracts the ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL field value from a register. */
#define ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG1_PORTB_SINGLE_CTL_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : PORT C SINGLE CTL - portc_single_ctl
 * 
 * Indicates the mode of operation of Port C to be software controlled only.
 * Ignored because there is no Port C in the GPIO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                 | Value | Description                             
 * :-----------------------------------------------------|:------|:-----------------------------------------
 *  ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL_E_SOFTCTLONLY | 0x1   | Software Enabled Individual Port Control
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL
 * 
 * Software Enabled Individual Port Control
 */
#define ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL_E_SOFTCTLONLY    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL_MSB        6
/* The width in bits of the ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL register field value. */
#define ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL_SET_MSK    0x00000040
/* The mask used to clear the ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL register field value. */
#define ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL_CLR_MSK    0xffffffbf
/* The reset value of the ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL_RESET      0x1
/* Extracts the ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL field value from a register. */
#define ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG1_PORTC_SINGLE_CTL_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : PORT D SINGLE CTL - portd_single_ctl
 * 
 * Indicates the mode of operation of Port D to be software controlled only.
 * Ignored because there is no Port D in the GPIO.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                 | Value | Description                             
 * :-----------------------------------------------------|:------|:-----------------------------------------
 *  ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL_E_SOFTCTLONLY | 0x1   | Software Enabled Individual Port Control
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL
 * 
 * Software Enabled Individual Port Control
 */
#define ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL_E_SOFTCTLONLY    0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL_MSB        7
/* The width in bits of the ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL register field value. */
#define ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL_SET_MSK    0x00000080
/* The mask used to clear the ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL register field value. */
#define ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL_CLR_MSK    0xffffff7f
/* The reset value of the ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL_RESET      0x1
/* Extracts the ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL field value from a register. */
#define ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG1_PORTD_SINGLE_CTL_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : HW PORTA - hw_porta
 * 
 * The value is fixed to enable Port A configuration to be controlled by software
 * only.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                         | Value | Description                           
 * :---------------------------------------------|:------|:---------------------------------------
 *  ALT_MON_GPIO_CFG_REG1_HW_PORTA_E_PORTANOHARD | 0x0   | Software Configuration Control Enabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG1_HW_PORTA
 * 
 * Software Configuration Control Enabled
 */
#define ALT_MON_GPIO_CFG_REG1_HW_PORTA_E_PORTANOHARD    0x0

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG1_HW_PORTA register field. */
#define ALT_MON_GPIO_CFG_REG1_HW_PORTA_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG1_HW_PORTA register field. */
#define ALT_MON_GPIO_CFG_REG1_HW_PORTA_MSB        8
/* The width in bits of the ALT_MON_GPIO_CFG_REG1_HW_PORTA register field. */
#define ALT_MON_GPIO_CFG_REG1_HW_PORTA_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_CFG_REG1_HW_PORTA register field value. */
#define ALT_MON_GPIO_CFG_REG1_HW_PORTA_SET_MSK    0x00000100
/* The mask used to clear the ALT_MON_GPIO_CFG_REG1_HW_PORTA register field value. */
#define ALT_MON_GPIO_CFG_REG1_HW_PORTA_CLR_MSK    0xfffffeff
/* The reset value of the ALT_MON_GPIO_CFG_REG1_HW_PORTA register field. */
#define ALT_MON_GPIO_CFG_REG1_HW_PORTA_RESET      0x0
/* Extracts the ALT_MON_GPIO_CFG_REG1_HW_PORTA field value from a register. */
#define ALT_MON_GPIO_CFG_REG1_HW_PORTA_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_MON_GPIO_CFG_REG1_HW_PORTA register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG1_HW_PORTA_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : Port A Interrupt Field - porta_intr
 * 
 * The value of this field is fixed to allow interrupts on Port A.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                           | Value | Description              
 * :-----------------------------------------------|:------|:--------------------------
 *  ALT_MON_GPIO_CFG_REG1_PORTA_INTR_E_PORTAINTERR | 0x1   | Port A Interrupts Enabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG1_PORTA_INTR
 * 
 * Port A Interrupts Enabled
 */
#define ALT_MON_GPIO_CFG_REG1_PORTA_INTR_E_PORTAINTERR  0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG1_PORTA_INTR register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_INTR_LSB        12
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG1_PORTA_INTR register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_INTR_MSB        12
/* The width in bits of the ALT_MON_GPIO_CFG_REG1_PORTA_INTR register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_INTR_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_CFG_REG1_PORTA_INTR register field value. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_INTR_SET_MSK    0x00001000
/* The mask used to clear the ALT_MON_GPIO_CFG_REG1_PORTA_INTR register field value. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_INTR_CLR_MSK    0xffffefff
/* The reset value of the ALT_MON_GPIO_CFG_REG1_PORTA_INTR register field. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_INTR_RESET      0x1
/* Extracts the ALT_MON_GPIO_CFG_REG1_PORTA_INTR field value from a register. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_INTR_GET(value) (((value) & 0x00001000) >> 12)
/* Produces a ALT_MON_GPIO_CFG_REG1_PORTA_INTR register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG1_PORTA_INTR_SET(value) (((value) << 12) & 0x00001000)

/*
 * Field : Debounce Field - debounce
 * 
 * The value of this field is fixed to not allow debouncing of the Port A signals.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                            | Value | Description         
 * :------------------------------------------------|:------|:---------------------
 *  ALT_MON_GPIO_CFG_REG1_DEBOUNCE_E_DEBOUNCEA_DISD | 0x0   | Debounce is Disabled
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG1_DEBOUNCE
 * 
 * Debounce is Disabled
 */
#define ALT_MON_GPIO_CFG_REG1_DEBOUNCE_E_DEBOUNCEA_DISD 0x0

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG1_DEBOUNCE register field. */
#define ALT_MON_GPIO_CFG_REG1_DEBOUNCE_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG1_DEBOUNCE register field. */
#define ALT_MON_GPIO_CFG_REG1_DEBOUNCE_MSB        13
/* The width in bits of the ALT_MON_GPIO_CFG_REG1_DEBOUNCE register field. */
#define ALT_MON_GPIO_CFG_REG1_DEBOUNCE_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_CFG_REG1_DEBOUNCE register field value. */
#define ALT_MON_GPIO_CFG_REG1_DEBOUNCE_SET_MSK    0x00002000
/* The mask used to clear the ALT_MON_GPIO_CFG_REG1_DEBOUNCE register field value. */
#define ALT_MON_GPIO_CFG_REG1_DEBOUNCE_CLR_MSK    0xffffdfff
/* The reset value of the ALT_MON_GPIO_CFG_REG1_DEBOUNCE register field. */
#define ALT_MON_GPIO_CFG_REG1_DEBOUNCE_RESET      0x0
/* Extracts the ALT_MON_GPIO_CFG_REG1_DEBOUNCE field value from a register. */
#define ALT_MON_GPIO_CFG_REG1_DEBOUNCE_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_MON_GPIO_CFG_REG1_DEBOUNCE register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG1_DEBOUNCE_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : Encoded GPIO Parameters Available - add_encoded_params
 * 
 * Fixed to allow the indentification of the Designware IP component.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                | Value | Description              
 * :----------------------------------------------------|:------|:--------------------------
 *  ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS_E_ADDENCPARAMS | 0x1   | Enable IP indentification
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS
 * 
 * Enable IP indentification
 */
#define ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS_E_ADDENCPARAMS 0x1

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS register field. */
#define ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS register field. */
#define ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS_MSB        14
/* The width in bits of the ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS register field. */
#define ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS register field value. */
#define ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS_SET_MSK    0x00004000
/* The mask used to clear the ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS register field value. */
#define ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS_CLR_MSK    0xffffbfff
/* The reset value of the ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS register field. */
#define ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS_RESET      0x1
/* Extracts the ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS field value from a register. */
#define ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG1_ADD_ENC_PARAMS_SET(value) (((value) << 14) & 0x00004000)

/*
 * Field : ID Field - gpio_id
 * 
 * Provides an ID code value
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                            | Value | Description                   
 * :------------------------------------------------|:------|:-------------------------------
 *  ALT_MON_GPIO_CFG_REG1_GPIO_ID_E_IDCODE_EXCLUDED | 0x0   | GPIO ID Code Register Excluded
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG1_GPIO_ID
 * 
 * GPIO ID Code Register Excluded
 */
#define ALT_MON_GPIO_CFG_REG1_GPIO_ID_E_IDCODE_EXCLUDED 0x0

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG1_GPIO_ID register field. */
#define ALT_MON_GPIO_CFG_REG1_GPIO_ID_LSB        15
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG1_GPIO_ID register field. */
#define ALT_MON_GPIO_CFG_REG1_GPIO_ID_MSB        15
/* The width in bits of the ALT_MON_GPIO_CFG_REG1_GPIO_ID register field. */
#define ALT_MON_GPIO_CFG_REG1_GPIO_ID_WIDTH      1
/* The mask used to set the ALT_MON_GPIO_CFG_REG1_GPIO_ID register field value. */
#define ALT_MON_GPIO_CFG_REG1_GPIO_ID_SET_MSK    0x00008000
/* The mask used to clear the ALT_MON_GPIO_CFG_REG1_GPIO_ID register field value. */
#define ALT_MON_GPIO_CFG_REG1_GPIO_ID_CLR_MSK    0xffff7fff
/* The reset value of the ALT_MON_GPIO_CFG_REG1_GPIO_ID register field. */
#define ALT_MON_GPIO_CFG_REG1_GPIO_ID_RESET      0x0
/* Extracts the ALT_MON_GPIO_CFG_REG1_GPIO_ID field value from a register. */
#define ALT_MON_GPIO_CFG_REG1_GPIO_ID_GET(value) (((value) & 0x00008000) >> 15)
/* Produces a ALT_MON_GPIO_CFG_REG1_GPIO_ID register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG1_GPIO_ID_SET(value) (((value) << 15) & 0x00008000)

/*
 * Field : Encoded ID Width Field - encoded_id_width
 * 
 * This value is fixed at 32 bits.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                            | Value | Description      
 * :------------------------------------------------|:------|:------------------
 *  ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH_E_ENCIDWIDTH | 0x1f  | Width of ID Field
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH
 * 
 * Width of ID Field
 */
#define ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH_E_ENCIDWIDTH 0x1f

/* The Least Significant Bit (LSB) position of the ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH register field. */
#define ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH register field. */
#define ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH_MSB        20
/* The width in bits of the ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH register field. */
#define ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH_WIDTH      5
/* The mask used to set the ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH register field value. */
#define ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH_SET_MSK    0x001f0000
/* The mask used to clear the ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH register field value. */
#define ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH_CLR_MSK    0xffe0ffff
/* The reset value of the ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH register field. */
#define ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH_RESET      0x1f
/* Extracts the ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH field value from a register. */
#define ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH_GET(value) (((value) & 0x001f0000) >> 16)
/* Produces a ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH register field value suitable for setting the register. */
#define ALT_MON_GPIO_CFG_REG1_ENC_ID_WIDTH_SET(value) (((value) << 16) & 0x001f0000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_MON_GPIO_CFG_REG1.
 */
struct ALT_MON_GPIO_CFG_REG1_s
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

/* The typedef declaration for register ALT_MON_GPIO_CFG_REG1. */
typedef volatile struct ALT_MON_GPIO_CFG_REG1_s  ALT_MON_GPIO_CFG_REG1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_MON_GPIO_CFG_REG1 register from the beginning of the component. */
#define ALT_MON_GPIO_CFG_REG1_OFST        0x74
/* The address of the ALT_MON_GPIO_CFG_REG1 register. */
#define ALT_MON_GPIO_CFG_REG1_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_MON_GPIO_CFG_REG1_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_MON.
 */
struct ALT_MON_s
{
    volatile uint32_t                      _pad_0x0_0x2f[12];   /* *UNDEFINED* */
    volatile ALT_MON_GPIO_INTEN_t          gpio_inten;          /* ALT_MON_GPIO_INTEN */
    volatile ALT_MON_GPIO_INTMSK_t         gpio_intmask;        /* ALT_MON_GPIO_INTMSK */
    volatile ALT_MON_GPIO_INTTYPE_LEVEL_t  gpio_inttype_level;  /* ALT_MON_GPIO_INTTYPE_LEVEL */
    volatile ALT_MON_GPIO_INT_POL_t        gpio_int_polarity;   /* ALT_MON_GPIO_INT_POL */
    volatile ALT_MON_GPIO_INTSTAT_t        gpio_intstatus;      /* ALT_MON_GPIO_INTSTAT */
    volatile ALT_MON_GPIO_RAW_INTSTAT_t    gpio_raw_intstatus;  /* ALT_MON_GPIO_RAW_INTSTAT */
    volatile uint32_t                      _pad_0x48_0x4b;      /* *UNDEFINED* */
    volatile ALT_MON_GPIO_PORTA_EOI_t      gpio_porta_eoi;      /* ALT_MON_GPIO_PORTA_EOI */
    volatile ALT_MON_GPIO_EXT_PORTA_t      gpio_ext_porta;      /* ALT_MON_GPIO_EXT_PORTA */
    volatile uint32_t                      _pad_0x54_0x5f[3];   /* *UNDEFINED* */
    volatile ALT_MON_GPIO_LS_SYNC_t        gpio_ls_sync;        /* ALT_MON_GPIO_LS_SYNC */
    volatile uint32_t                      _pad_0x64_0x6b[2];   /* *UNDEFINED* */
    volatile ALT_MON_GPIO_VER_ID_CODE_t    gpio_ver_id_code;    /* ALT_MON_GPIO_VER_ID_CODE */
    volatile ALT_MON_GPIO_CFG_REG2_t       gpio_config_reg2;    /* ALT_MON_GPIO_CFG_REG2 */
    volatile ALT_MON_GPIO_CFG_REG1_t       gpio_config_reg1;    /* ALT_MON_GPIO_CFG_REG1 */
    volatile uint32_t                      _pad_0x78_0x80[2];   /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_MON. */
typedef volatile struct ALT_MON_s  ALT_MON_t;
/* The struct declaration for the raw register contents of register group ALT_MON. */
struct ALT_MON_raw_s
{
    volatile uint32_t  _pad_0x0_0x2f[12];   /* *UNDEFINED* */
    volatile uint32_t  gpio_inten;          /* ALT_MON_GPIO_INTEN */
    volatile uint32_t  gpio_intmask;        /* ALT_MON_GPIO_INTMSK */
    volatile uint32_t  gpio_inttype_level;  /* ALT_MON_GPIO_INTTYPE_LEVEL */
    volatile uint32_t  gpio_int_polarity;   /* ALT_MON_GPIO_INT_POL */
    volatile uint32_t  gpio_intstatus;      /* ALT_MON_GPIO_INTSTAT */
    volatile uint32_t  gpio_raw_intstatus;  /* ALT_MON_GPIO_RAW_INTSTAT */
    volatile uint32_t  _pad_0x48_0x4b;      /* *UNDEFINED* */
    volatile uint32_t  gpio_porta_eoi;      /* ALT_MON_GPIO_PORTA_EOI */
    volatile uint32_t  gpio_ext_porta;      /* ALT_MON_GPIO_EXT_PORTA */
    volatile uint32_t  _pad_0x54_0x5f[3];   /* *UNDEFINED* */
    volatile uint32_t  gpio_ls_sync;        /* ALT_MON_GPIO_LS_SYNC */
    volatile uint32_t  _pad_0x64_0x6b[2];   /* *UNDEFINED* */
    volatile uint32_t  gpio_ver_id_code;    /* ALT_MON_GPIO_VER_ID_CODE */
    volatile uint32_t  gpio_config_reg2;    /* ALT_MON_GPIO_CFG_REG2 */
    volatile uint32_t  gpio_config_reg1;    /* ALT_MON_GPIO_CFG_REG1 */
    volatile uint32_t  _pad_0x78_0x80[2];   /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_MON. */
typedef volatile struct ALT_MON_raw_s  ALT_MON_raw_t;
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
 * The struct declaration for register group ALT_FPGAMGR.
 */
struct ALT_FPGAMGR_s
{
    volatile ALT_FPGAMGR_STAT_t      stat;                    /* ALT_FPGAMGR_STAT */
    volatile ALT_FPGAMGR_CTL_t       ctrl;                    /* ALT_FPGAMGR_CTL */
    volatile ALT_FPGAMGR_DCLKCNT_t   dclkcnt;                 /* ALT_FPGAMGR_DCLKCNT */
    volatile ALT_FPGAMGR_DCLKSTAT_t  dclkstat;                /* ALT_FPGAMGR_DCLKSTAT */
    volatile ALT_FPGAMGR_GPO_t       gpo;                     /* ALT_FPGAMGR_GPO */
    volatile ALT_FPGAMGR_GPI_t       gpi;                     /* ALT_FPGAMGR_GPI */
    volatile ALT_FPGAMGR_MISCI_t     misci;                   /* ALT_FPGAMGR_MISCI */
    volatile uint32_t                _pad_0x1c_0x7ff[505];    /* *UNDEFINED* */
    volatile ALT_MON_t               mon;                     /* ALT_MON */
    volatile uint32_t                _pad_0x880_0x1000[480];  /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_FPGAMGR. */
typedef volatile struct ALT_FPGAMGR_s  ALT_FPGAMGR_t;
/* The struct declaration for the raw register contents of register group ALT_FPGAMGR. */
struct ALT_FPGAMGR_raw_s
{
    volatile uint32_t       stat;                    /* ALT_FPGAMGR_STAT */
    volatile uint32_t       ctrl;                    /* ALT_FPGAMGR_CTL */
    volatile uint32_t       dclkcnt;                 /* ALT_FPGAMGR_DCLKCNT */
    volatile uint32_t       dclkstat;                /* ALT_FPGAMGR_DCLKSTAT */
    volatile uint32_t       gpo;                     /* ALT_FPGAMGR_GPO */
    volatile uint32_t       gpi;                     /* ALT_FPGAMGR_GPI */
    volatile uint32_t       misci;                   /* ALT_FPGAMGR_MISCI */
    volatile uint32_t       _pad_0x1c_0x7ff[505];    /* *UNDEFINED* */
    volatile ALT_MON_raw_t  mon;                     /* ALT_MON */
    volatile uint32_t       _pad_0x880_0x1000[480];  /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_FPGAMGR. */
typedef volatile struct ALT_FPGAMGR_raw_s  ALT_FPGAMGR_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_FPGAMGR_H__ */

