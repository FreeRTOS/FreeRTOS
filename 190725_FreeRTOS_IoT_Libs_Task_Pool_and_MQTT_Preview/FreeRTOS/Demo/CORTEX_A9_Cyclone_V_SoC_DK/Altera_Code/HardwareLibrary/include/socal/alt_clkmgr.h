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

/* Altera - ALT_CLKMGR */

#ifndef __ALTERA_ALT_CLKMGR_H__
#define __ALTERA_ALT_CLKMGR_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : Clock Manager Module - ALT_CLKMGR
 * Clock Manager Module
 * 
 * Registers in the Clock Manager module
 * 
 */
/*
 * Register : Control Register - ctrl
 * 
 * Contains fields that control the entire Clock Manager.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                  
 * :-------|:-------|:------|:------------------------------
 *  [0]    | RW     | 0x1   | Safe Mode                    
 *  [1]    | ???    | 0x0   | *UNDEFINED*                  
 *  [2]    | RW     | 0x1   | Enable SafeMode on Warm Reset
 *  [31:3] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : Safe Mode - safemode
 * 
 * When set the Clock Manager is in Safe Mode.
 * 
 * In Safe Mode Clock Manager register settings defining clock behavior are ignored
 * and clocks are set to a Safe Mode state.In Safe Mode all clocks with the
 * optional exception of debug clocks, are directly generated from the EOSC1 clock
 * input, all PLLs are bypassed, all programmable dividers are set to 1 and all
 * clocks are enabled.
 * 
 * This bit should only be cleared when clocks have been correctly configured
 * 
 * This field is set on a cold reset and optionally on a warm reset and may not be
 * set by SW.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_CTL_SAFEMOD register field. */
#define ALT_CLKMGR_CTL_SAFEMOD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_CTL_SAFEMOD register field. */
#define ALT_CLKMGR_CTL_SAFEMOD_MSB        0
/* The width in bits of the ALT_CLKMGR_CTL_SAFEMOD register field. */
#define ALT_CLKMGR_CTL_SAFEMOD_WIDTH      1
/* The mask used to set the ALT_CLKMGR_CTL_SAFEMOD register field value. */
#define ALT_CLKMGR_CTL_SAFEMOD_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_CTL_SAFEMOD register field value. */
#define ALT_CLKMGR_CTL_SAFEMOD_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_CTL_SAFEMOD register field. */
#define ALT_CLKMGR_CTL_SAFEMOD_RESET      0x1
/* Extracts the ALT_CLKMGR_CTL_SAFEMOD field value from a register. */
#define ALT_CLKMGR_CTL_SAFEMOD_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_CTL_SAFEMOD register field value suitable for setting the register. */
#define ALT_CLKMGR_CTL_SAFEMOD_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Enable SafeMode on Warm Reset - ensfmdwr
 * 
 * When set the Clock Manager will respond to a Safe Mode request from the Reset
 * Manager on a warm reset by setting the Safe Mode bit. When clear the clock
 * manager will not set the the Safe Mode bit on a warm reset This bit is cleared
 * on a cold reset. Warm reset has no affect on this bit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_CTL_ENSFMDWR register field. */
#define ALT_CLKMGR_CTL_ENSFMDWR_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_CTL_ENSFMDWR register field. */
#define ALT_CLKMGR_CTL_ENSFMDWR_MSB        2
/* The width in bits of the ALT_CLKMGR_CTL_ENSFMDWR register field. */
#define ALT_CLKMGR_CTL_ENSFMDWR_WIDTH      1
/* The mask used to set the ALT_CLKMGR_CTL_ENSFMDWR register field value. */
#define ALT_CLKMGR_CTL_ENSFMDWR_SET_MSK    0x00000004
/* The mask used to clear the ALT_CLKMGR_CTL_ENSFMDWR register field value. */
#define ALT_CLKMGR_CTL_ENSFMDWR_CLR_MSK    0xfffffffb
/* The reset value of the ALT_CLKMGR_CTL_ENSFMDWR register field. */
#define ALT_CLKMGR_CTL_ENSFMDWR_RESET      0x1
/* Extracts the ALT_CLKMGR_CTL_ENSFMDWR field value from a register. */
#define ALT_CLKMGR_CTL_ENSFMDWR_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_CLKMGR_CTL_ENSFMDWR register field value suitable for setting the register. */
#define ALT_CLKMGR_CTL_ENSFMDWR_SET(value) (((value) << 2) & 0x00000004)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_CTL.
 */
struct ALT_CLKMGR_CTL_s
{
    uint32_t  safemode :  1;  /* Safe Mode */
    uint32_t           :  1;  /* *UNDEFINED* */
    uint32_t  ensfmdwr :  1;  /* Enable SafeMode on Warm Reset */
    uint32_t           : 29;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_CTL. */
typedef volatile struct ALT_CLKMGR_CTL_s  ALT_CLKMGR_CTL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_CTL register from the beginning of the component. */
#define ALT_CLKMGR_CTL_OFST        0x0

/*
 * Register : PLL Bypass Register - bypass
 * 
 * Contains fields that control bypassing each PLL.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                 
 * :-------|:-------|:------|:-----------------------------
 *  [0]    | RW     | 0x1   | Main PLL Bypass             
 *  [1]    | RW     | 0x1   | SDRAM PLL Bypass            
 *  [2]    | RW     | 0x0   | SDRAM PLL Bypass Source     
 *  [3]    | RW     | 0x1   | Peripheral PLL Bypass       
 *  [4]    | RW     | 0x0   | Peripheral PLL Bypass Source
 *  [31:5] | ???    | 0x0   | *UNDEFINED*                 
 * 
 */
/*
 * Field : Main PLL Bypass - mainpll
 * 
 * When set, causes the Main PLL VCO and counters to be bypassed so that all clocks
 * generated by the Main PLL are directly driven from the Main PLL input clock. The
 * bypass source for Main PLL is the external eosc1_clk.
 * 
 * The reset value for this bit is applied on a cold reset.   Warm reset has no
 * affect on this bit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_BYPASS_MAINPLL register field. */
#define ALT_CLKMGR_BYPASS_MAINPLL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_BYPASS_MAINPLL register field. */
#define ALT_CLKMGR_BYPASS_MAINPLL_MSB        0
/* The width in bits of the ALT_CLKMGR_BYPASS_MAINPLL register field. */
#define ALT_CLKMGR_BYPASS_MAINPLL_WIDTH      1
/* The mask used to set the ALT_CLKMGR_BYPASS_MAINPLL register field value. */
#define ALT_CLKMGR_BYPASS_MAINPLL_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_BYPASS_MAINPLL register field value. */
#define ALT_CLKMGR_BYPASS_MAINPLL_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_BYPASS_MAINPLL register field. */
#define ALT_CLKMGR_BYPASS_MAINPLL_RESET      0x1
/* Extracts the ALT_CLKMGR_BYPASS_MAINPLL field value from a register. */
#define ALT_CLKMGR_BYPASS_MAINPLL_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_BYPASS_MAINPLL register field value suitable for setting the register. */
#define ALT_CLKMGR_BYPASS_MAINPLL_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : SDRAM PLL Bypass - sdrpll
 * 
 * When set, causes the SDRAM PLL VCO and counters to be bypassed so that all
 * clocks generated by the SDRAM PLL are directly driven from either eosc1_clk or
 * the SDRAM PLL input clock.
 * 
 * The bypass clock source for SDRAM PLL is determined by the SDRAM PLL Bypass
 * Source Register bit.
 * 
 * The reset value for this bit is applied on a cold reset.   Warm reset has no
 * affect on this bit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_BYPASS_SDRPLL register field. */
#define ALT_CLKMGR_BYPASS_SDRPLL_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_BYPASS_SDRPLL register field. */
#define ALT_CLKMGR_BYPASS_SDRPLL_MSB        1
/* The width in bits of the ALT_CLKMGR_BYPASS_SDRPLL register field. */
#define ALT_CLKMGR_BYPASS_SDRPLL_WIDTH      1
/* The mask used to set the ALT_CLKMGR_BYPASS_SDRPLL register field value. */
#define ALT_CLKMGR_BYPASS_SDRPLL_SET_MSK    0x00000002
/* The mask used to clear the ALT_CLKMGR_BYPASS_SDRPLL register field value. */
#define ALT_CLKMGR_BYPASS_SDRPLL_CLR_MSK    0xfffffffd
/* The reset value of the ALT_CLKMGR_BYPASS_SDRPLL register field. */
#define ALT_CLKMGR_BYPASS_SDRPLL_RESET      0x1
/* Extracts the ALT_CLKMGR_BYPASS_SDRPLL field value from a register. */
#define ALT_CLKMGR_BYPASS_SDRPLL_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_CLKMGR_BYPASS_SDRPLL register field value suitable for setting the register. */
#define ALT_CLKMGR_BYPASS_SDRPLL_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : SDRAM PLL Bypass Source - sdrpllsrc
 * 
 * This bit defines the bypass source forSDRAM PLL.
 * 
 * When changing fields that affect VCO lock the PLL must be bypassed and this bit
 * must be set to OSC1_CLK.
 * 
 * The reset value for this bit is applied on a cold reset.   Warm reset has no
 * affect on this bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                           | Value | Description         
 * :-----------------------------------------------|:------|:---------------------
 *  ALT_CLKMGR_BYPASS_SDRPLLSRC_E_SELECT_EOSC1     | 0x0   | Select EOSC1        
 *  ALT_CLKMGR_BYPASS_SDRPLLSRC_E_SELECT_INPUT_MUX | 0x1   | Select PLL Input Mux
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_BYPASS_SDRPLLSRC
 * 
 * Select EOSC1
 */
#define ALT_CLKMGR_BYPASS_SDRPLLSRC_E_SELECT_EOSC1      0x0
/*
 * Enumerated value for register field ALT_CLKMGR_BYPASS_SDRPLLSRC
 * 
 * Select PLL Input Mux
 */
#define ALT_CLKMGR_BYPASS_SDRPLLSRC_E_SELECT_INPUT_MUX  0x1

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_BYPASS_SDRPLLSRC register field. */
#define ALT_CLKMGR_BYPASS_SDRPLLSRC_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_BYPASS_SDRPLLSRC register field. */
#define ALT_CLKMGR_BYPASS_SDRPLLSRC_MSB        2
/* The width in bits of the ALT_CLKMGR_BYPASS_SDRPLLSRC register field. */
#define ALT_CLKMGR_BYPASS_SDRPLLSRC_WIDTH      1
/* The mask used to set the ALT_CLKMGR_BYPASS_SDRPLLSRC register field value. */
#define ALT_CLKMGR_BYPASS_SDRPLLSRC_SET_MSK    0x00000004
/* The mask used to clear the ALT_CLKMGR_BYPASS_SDRPLLSRC register field value. */
#define ALT_CLKMGR_BYPASS_SDRPLLSRC_CLR_MSK    0xfffffffb
/* The reset value of the ALT_CLKMGR_BYPASS_SDRPLLSRC register field. */
#define ALT_CLKMGR_BYPASS_SDRPLLSRC_RESET      0x0
/* Extracts the ALT_CLKMGR_BYPASS_SDRPLLSRC field value from a register. */
#define ALT_CLKMGR_BYPASS_SDRPLLSRC_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_CLKMGR_BYPASS_SDRPLLSRC register field value suitable for setting the register. */
#define ALT_CLKMGR_BYPASS_SDRPLLSRC_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Peripheral PLL Bypass - perpll
 * 
 * When set, causes the Peripheral PLL VCO and counters to be bypassed so that all
 * clocks generated by the Peripheral PLL are directly driven from either eosc1_clk
 * or the Peripheral PLL input clock.
 * 
 * The bypass clock source for Peripheral PLL is determined by the Peripheral PLL
 * Bypass Source Register bit.
 * 
 * The reset value for this bit is applied on a cold reset.   Warm reset has no
 * affect on this bit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_BYPASS_PERPLL register field. */
#define ALT_CLKMGR_BYPASS_PERPLL_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_BYPASS_PERPLL register field. */
#define ALT_CLKMGR_BYPASS_PERPLL_MSB        3
/* The width in bits of the ALT_CLKMGR_BYPASS_PERPLL register field. */
#define ALT_CLKMGR_BYPASS_PERPLL_WIDTH      1
/* The mask used to set the ALT_CLKMGR_BYPASS_PERPLL register field value. */
#define ALT_CLKMGR_BYPASS_PERPLL_SET_MSK    0x00000008
/* The mask used to clear the ALT_CLKMGR_BYPASS_PERPLL register field value. */
#define ALT_CLKMGR_BYPASS_PERPLL_CLR_MSK    0xfffffff7
/* The reset value of the ALT_CLKMGR_BYPASS_PERPLL register field. */
#define ALT_CLKMGR_BYPASS_PERPLL_RESET      0x1
/* Extracts the ALT_CLKMGR_BYPASS_PERPLL field value from a register. */
#define ALT_CLKMGR_BYPASS_PERPLL_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_CLKMGR_BYPASS_PERPLL register field value suitable for setting the register. */
#define ALT_CLKMGR_BYPASS_PERPLL_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Peripheral PLL Bypass Source - perpllsrc
 * 
 * This bit defines the bypass source forPeripheral PLL.
 * 
 * When changing fields that affect VCO lock the PLL must be bypassed and this bit
 * must be set to OSC1_CLK.
 * 
 * The reset value for this bit is applied on a cold reset.   Warm reset has no
 * affect on this bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                           | Value | Description         
 * :-----------------------------------------------|:------|:---------------------
 *  ALT_CLKMGR_BYPASS_PERPLLSRC_E_SELECT_EOSC1     | 0x0   | Select EOSC1        
 *  ALT_CLKMGR_BYPASS_PERPLLSRC_E_SELECT_INPUT_MUX | 0x1   | Select PLL Input Mux
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_BYPASS_PERPLLSRC
 * 
 * Select EOSC1
 */
#define ALT_CLKMGR_BYPASS_PERPLLSRC_E_SELECT_EOSC1      0x0
/*
 * Enumerated value for register field ALT_CLKMGR_BYPASS_PERPLLSRC
 * 
 * Select PLL Input Mux
 */
#define ALT_CLKMGR_BYPASS_PERPLLSRC_E_SELECT_INPUT_MUX  0x1

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_BYPASS_PERPLLSRC register field. */
#define ALT_CLKMGR_BYPASS_PERPLLSRC_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_BYPASS_PERPLLSRC register field. */
#define ALT_CLKMGR_BYPASS_PERPLLSRC_MSB        4
/* The width in bits of the ALT_CLKMGR_BYPASS_PERPLLSRC register field. */
#define ALT_CLKMGR_BYPASS_PERPLLSRC_WIDTH      1
/* The mask used to set the ALT_CLKMGR_BYPASS_PERPLLSRC register field value. */
#define ALT_CLKMGR_BYPASS_PERPLLSRC_SET_MSK    0x00000010
/* The mask used to clear the ALT_CLKMGR_BYPASS_PERPLLSRC register field value. */
#define ALT_CLKMGR_BYPASS_PERPLLSRC_CLR_MSK    0xffffffef
/* The reset value of the ALT_CLKMGR_BYPASS_PERPLLSRC register field. */
#define ALT_CLKMGR_BYPASS_PERPLLSRC_RESET      0x0
/* Extracts the ALT_CLKMGR_BYPASS_PERPLLSRC field value from a register. */
#define ALT_CLKMGR_BYPASS_PERPLLSRC_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_CLKMGR_BYPASS_PERPLLSRC register field value suitable for setting the register. */
#define ALT_CLKMGR_BYPASS_PERPLLSRC_SET(value) (((value) << 4) & 0x00000010)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_BYPASS.
 */
struct ALT_CLKMGR_BYPASS_s
{
    uint32_t  mainpll   :  1;  /* Main PLL Bypass */
    uint32_t  sdrpll    :  1;  /* SDRAM PLL Bypass */
    uint32_t  sdrpllsrc :  1;  /* SDRAM PLL Bypass Source */
    uint32_t  perpll    :  1;  /* Peripheral PLL Bypass */
    uint32_t  perpllsrc :  1;  /* Peripheral PLL Bypass Source */
    uint32_t            : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_BYPASS. */
typedef volatile struct ALT_CLKMGR_BYPASS_s  ALT_CLKMGR_BYPASS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_BYPASS register from the beginning of the component. */
#define ALT_CLKMGR_BYPASS_OFST        0x4

/*
 * Register : Interrupt Status Register - inter
 * 
 * Contains fields that indicate the PLL lock status.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset   | Description                       
 * :-------|:-------|:--------|:-----------------------------------
 *  [0]    | RW     | 0x0     | Main PLL Achieved Lock            
 *  [1]    | RW     | 0x0     | Peripheral PLL Achieved Lock      
 *  [2]    | RW     | 0x0     | SDRAM PLL Achieved Lock           
 *  [3]    | RW     | 0x0     | Main PLL Lost Lock                
 *  [4]    | RW     | 0x0     | Peripheral PLL Lost Lock          
 *  [5]    | RW     | 0x0     | SDRAM PLL Lost Lock               
 *  [6]    | R      | Unknown | Main PLL Current Lock Status      
 *  [7]    | R      | Unknown | Peripheral PLL Current Lock Status
 *  [8]    | R      | Unknown | SDRAM PLL Current Lock Status     
 *  [31:9] | ???    | 0x0     | *UNDEFINED*                       
 * 
 */
/*
 * Field : Main PLL Achieved Lock - mainpllachieved
 * 
 * If 1, the Main PLL has achieved lock at least once since this bit was cleared.
 * If 0, the Main PLL has not achieved lock since this bit was cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTER_MAINPLLACHIEVED register field. */
#define ALT_CLKMGR_INTER_MAINPLLACHIEVED_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTER_MAINPLLACHIEVED register field. */
#define ALT_CLKMGR_INTER_MAINPLLACHIEVED_MSB        0
/* The width in bits of the ALT_CLKMGR_INTER_MAINPLLACHIEVED register field. */
#define ALT_CLKMGR_INTER_MAINPLLACHIEVED_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTER_MAINPLLACHIEVED register field value. */
#define ALT_CLKMGR_INTER_MAINPLLACHIEVED_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_INTER_MAINPLLACHIEVED register field value. */
#define ALT_CLKMGR_INTER_MAINPLLACHIEVED_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_INTER_MAINPLLACHIEVED register field. */
#define ALT_CLKMGR_INTER_MAINPLLACHIEVED_RESET      0x0
/* Extracts the ALT_CLKMGR_INTER_MAINPLLACHIEVED field value from a register. */
#define ALT_CLKMGR_INTER_MAINPLLACHIEVED_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_INTER_MAINPLLACHIEVED register field value suitable for setting the register. */
#define ALT_CLKMGR_INTER_MAINPLLACHIEVED_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Peripheral PLL Achieved Lock - perpllachieved
 * 
 * If 1, the Peripheral PLL has achieved lock at least once since this bit was
 * cleared. If 0, the Peripheral PLL has not achieved lock since this bit was
 * cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTER_PERPLLACHIEVED register field. */
#define ALT_CLKMGR_INTER_PERPLLACHIEVED_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTER_PERPLLACHIEVED register field. */
#define ALT_CLKMGR_INTER_PERPLLACHIEVED_MSB        1
/* The width in bits of the ALT_CLKMGR_INTER_PERPLLACHIEVED register field. */
#define ALT_CLKMGR_INTER_PERPLLACHIEVED_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTER_PERPLLACHIEVED register field value. */
#define ALT_CLKMGR_INTER_PERPLLACHIEVED_SET_MSK    0x00000002
/* The mask used to clear the ALT_CLKMGR_INTER_PERPLLACHIEVED register field value. */
#define ALT_CLKMGR_INTER_PERPLLACHIEVED_CLR_MSK    0xfffffffd
/* The reset value of the ALT_CLKMGR_INTER_PERPLLACHIEVED register field. */
#define ALT_CLKMGR_INTER_PERPLLACHIEVED_RESET      0x0
/* Extracts the ALT_CLKMGR_INTER_PERPLLACHIEVED field value from a register. */
#define ALT_CLKMGR_INTER_PERPLLACHIEVED_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_CLKMGR_INTER_PERPLLACHIEVED register field value suitable for setting the register. */
#define ALT_CLKMGR_INTER_PERPLLACHIEVED_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : SDRAM PLL Achieved Lock - sdrpllachieved
 * 
 * If 1, the SDRAM PLL has achieved lock at least once since this bit was cleared.
 * If 0, the SDRAM PLL has not achieved lock since this bit was cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTER_SDRPLLACHIEVED register field. */
#define ALT_CLKMGR_INTER_SDRPLLACHIEVED_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTER_SDRPLLACHIEVED register field. */
#define ALT_CLKMGR_INTER_SDRPLLACHIEVED_MSB        2
/* The width in bits of the ALT_CLKMGR_INTER_SDRPLLACHIEVED register field. */
#define ALT_CLKMGR_INTER_SDRPLLACHIEVED_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTER_SDRPLLACHIEVED register field value. */
#define ALT_CLKMGR_INTER_SDRPLLACHIEVED_SET_MSK    0x00000004
/* The mask used to clear the ALT_CLKMGR_INTER_SDRPLLACHIEVED register field value. */
#define ALT_CLKMGR_INTER_SDRPLLACHIEVED_CLR_MSK    0xfffffffb
/* The reset value of the ALT_CLKMGR_INTER_SDRPLLACHIEVED register field. */
#define ALT_CLKMGR_INTER_SDRPLLACHIEVED_RESET      0x0
/* Extracts the ALT_CLKMGR_INTER_SDRPLLACHIEVED field value from a register. */
#define ALT_CLKMGR_INTER_SDRPLLACHIEVED_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_CLKMGR_INTER_SDRPLLACHIEVED register field value suitable for setting the register. */
#define ALT_CLKMGR_INTER_SDRPLLACHIEVED_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Main PLL Lost Lock - mainplllost
 * 
 * If 1, the Main PLL has lost lock at least once since this bit was cleared. If 0,
 * the Main PLL has not lost lock since this bit was cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTER_MAINPLLLOST register field. */
#define ALT_CLKMGR_INTER_MAINPLLLOST_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTER_MAINPLLLOST register field. */
#define ALT_CLKMGR_INTER_MAINPLLLOST_MSB        3
/* The width in bits of the ALT_CLKMGR_INTER_MAINPLLLOST register field. */
#define ALT_CLKMGR_INTER_MAINPLLLOST_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTER_MAINPLLLOST register field value. */
#define ALT_CLKMGR_INTER_MAINPLLLOST_SET_MSK    0x00000008
/* The mask used to clear the ALT_CLKMGR_INTER_MAINPLLLOST register field value. */
#define ALT_CLKMGR_INTER_MAINPLLLOST_CLR_MSK    0xfffffff7
/* The reset value of the ALT_CLKMGR_INTER_MAINPLLLOST register field. */
#define ALT_CLKMGR_INTER_MAINPLLLOST_RESET      0x0
/* Extracts the ALT_CLKMGR_INTER_MAINPLLLOST field value from a register. */
#define ALT_CLKMGR_INTER_MAINPLLLOST_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_CLKMGR_INTER_MAINPLLLOST register field value suitable for setting the register. */
#define ALT_CLKMGR_INTER_MAINPLLLOST_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Peripheral PLL Lost Lock - perplllost
 * 
 * If 1, the Peripheral PLL has lost lock at least once since this bit was cleared.
 * If 0, the Peripheral PLL has not lost lock since this bit was cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTER_PERPLLLOST register field. */
#define ALT_CLKMGR_INTER_PERPLLLOST_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTER_PERPLLLOST register field. */
#define ALT_CLKMGR_INTER_PERPLLLOST_MSB        4
/* The width in bits of the ALT_CLKMGR_INTER_PERPLLLOST register field. */
#define ALT_CLKMGR_INTER_PERPLLLOST_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTER_PERPLLLOST register field value. */
#define ALT_CLKMGR_INTER_PERPLLLOST_SET_MSK    0x00000010
/* The mask used to clear the ALT_CLKMGR_INTER_PERPLLLOST register field value. */
#define ALT_CLKMGR_INTER_PERPLLLOST_CLR_MSK    0xffffffef
/* The reset value of the ALT_CLKMGR_INTER_PERPLLLOST register field. */
#define ALT_CLKMGR_INTER_PERPLLLOST_RESET      0x0
/* Extracts the ALT_CLKMGR_INTER_PERPLLLOST field value from a register. */
#define ALT_CLKMGR_INTER_PERPLLLOST_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_CLKMGR_INTER_PERPLLLOST register field value suitable for setting the register. */
#define ALT_CLKMGR_INTER_PERPLLLOST_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : SDRAM PLL Lost Lock - sdrplllost
 * 
 * If 1, the SDRAM PLL has lost lock at least once since this bit was cleared. If
 * 0, the SDRAM PLL has not lost lock since this bit was cleared.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTER_SDRPLLLOST register field. */
#define ALT_CLKMGR_INTER_SDRPLLLOST_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTER_SDRPLLLOST register field. */
#define ALT_CLKMGR_INTER_SDRPLLLOST_MSB        5
/* The width in bits of the ALT_CLKMGR_INTER_SDRPLLLOST register field. */
#define ALT_CLKMGR_INTER_SDRPLLLOST_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTER_SDRPLLLOST register field value. */
#define ALT_CLKMGR_INTER_SDRPLLLOST_SET_MSK    0x00000020
/* The mask used to clear the ALT_CLKMGR_INTER_SDRPLLLOST register field value. */
#define ALT_CLKMGR_INTER_SDRPLLLOST_CLR_MSK    0xffffffdf
/* The reset value of the ALT_CLKMGR_INTER_SDRPLLLOST register field. */
#define ALT_CLKMGR_INTER_SDRPLLLOST_RESET      0x0
/* Extracts the ALT_CLKMGR_INTER_SDRPLLLOST field value from a register. */
#define ALT_CLKMGR_INTER_SDRPLLLOST_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_CLKMGR_INTER_SDRPLLLOST register field value suitable for setting the register. */
#define ALT_CLKMGR_INTER_SDRPLLLOST_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Main PLL Current Lock Status - mainplllocked
 * 
 * If 1, the Main PLL is currently locked. If 0, the Main PLL is currently not
 * locked.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTER_MAINPLLLOCKED register field. */
#define ALT_CLKMGR_INTER_MAINPLLLOCKED_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTER_MAINPLLLOCKED register field. */
#define ALT_CLKMGR_INTER_MAINPLLLOCKED_MSB        6
/* The width in bits of the ALT_CLKMGR_INTER_MAINPLLLOCKED register field. */
#define ALT_CLKMGR_INTER_MAINPLLLOCKED_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTER_MAINPLLLOCKED register field value. */
#define ALT_CLKMGR_INTER_MAINPLLLOCKED_SET_MSK    0x00000040
/* The mask used to clear the ALT_CLKMGR_INTER_MAINPLLLOCKED register field value. */
#define ALT_CLKMGR_INTER_MAINPLLLOCKED_CLR_MSK    0xffffffbf
/* The reset value of the ALT_CLKMGR_INTER_MAINPLLLOCKED register field is UNKNOWN. */
#define ALT_CLKMGR_INTER_MAINPLLLOCKED_RESET      0x0
/* Extracts the ALT_CLKMGR_INTER_MAINPLLLOCKED field value from a register. */
#define ALT_CLKMGR_INTER_MAINPLLLOCKED_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_CLKMGR_INTER_MAINPLLLOCKED register field value suitable for setting the register. */
#define ALT_CLKMGR_INTER_MAINPLLLOCKED_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Peripheral PLL Current Lock Status - perplllocked
 * 
 * If 1, the Peripheral PLL is currently locked. If 0, the Peripheral PLL is
 * currently not locked.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTER_PERPLLLOCKED register field. */
#define ALT_CLKMGR_INTER_PERPLLLOCKED_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTER_PERPLLLOCKED register field. */
#define ALT_CLKMGR_INTER_PERPLLLOCKED_MSB        7
/* The width in bits of the ALT_CLKMGR_INTER_PERPLLLOCKED register field. */
#define ALT_CLKMGR_INTER_PERPLLLOCKED_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTER_PERPLLLOCKED register field value. */
#define ALT_CLKMGR_INTER_PERPLLLOCKED_SET_MSK    0x00000080
/* The mask used to clear the ALT_CLKMGR_INTER_PERPLLLOCKED register field value. */
#define ALT_CLKMGR_INTER_PERPLLLOCKED_CLR_MSK    0xffffff7f
/* The reset value of the ALT_CLKMGR_INTER_PERPLLLOCKED register field is UNKNOWN. */
#define ALT_CLKMGR_INTER_PERPLLLOCKED_RESET      0x0
/* Extracts the ALT_CLKMGR_INTER_PERPLLLOCKED field value from a register. */
#define ALT_CLKMGR_INTER_PERPLLLOCKED_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_CLKMGR_INTER_PERPLLLOCKED register field value suitable for setting the register. */
#define ALT_CLKMGR_INTER_PERPLLLOCKED_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : SDRAM PLL Current Lock Status - sdrplllocked
 * 
 * If 1, the SDRAM PLL is currently locked. If 0, the SDRAM PLL is currently not
 * locked.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTER_SDRPLLLOCKED register field. */
#define ALT_CLKMGR_INTER_SDRPLLLOCKED_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTER_SDRPLLLOCKED register field. */
#define ALT_CLKMGR_INTER_SDRPLLLOCKED_MSB        8
/* The width in bits of the ALT_CLKMGR_INTER_SDRPLLLOCKED register field. */
#define ALT_CLKMGR_INTER_SDRPLLLOCKED_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTER_SDRPLLLOCKED register field value. */
#define ALT_CLKMGR_INTER_SDRPLLLOCKED_SET_MSK    0x00000100
/* The mask used to clear the ALT_CLKMGR_INTER_SDRPLLLOCKED register field value. */
#define ALT_CLKMGR_INTER_SDRPLLLOCKED_CLR_MSK    0xfffffeff
/* The reset value of the ALT_CLKMGR_INTER_SDRPLLLOCKED register field is UNKNOWN. */
#define ALT_CLKMGR_INTER_SDRPLLLOCKED_RESET      0x0
/* Extracts the ALT_CLKMGR_INTER_SDRPLLLOCKED field value from a register. */
#define ALT_CLKMGR_INTER_SDRPLLLOCKED_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_CLKMGR_INTER_SDRPLLLOCKED register field value suitable for setting the register. */
#define ALT_CLKMGR_INTER_SDRPLLLOCKED_SET(value) (((value) << 8) & 0x00000100)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_INTER.
 */
struct ALT_CLKMGR_INTER_s
{
    uint32_t        mainpllachieved :  1;  /* Main PLL Achieved Lock */
    uint32_t        perpllachieved  :  1;  /* Peripheral PLL Achieved Lock */
    uint32_t        sdrpllachieved  :  1;  /* SDRAM PLL Achieved Lock */
    uint32_t        mainplllost     :  1;  /* Main PLL Lost Lock */
    uint32_t        perplllost      :  1;  /* Peripheral PLL Lost Lock */
    uint32_t        sdrplllost      :  1;  /* SDRAM PLL Lost Lock */
    const uint32_t  mainplllocked   :  1;  /* Main PLL Current Lock Status */
    const uint32_t  perplllocked    :  1;  /* Peripheral PLL Current Lock Status */
    const uint32_t  sdrplllocked    :  1;  /* SDRAM PLL Current Lock Status */
    uint32_t                        : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_INTER. */
typedef volatile struct ALT_CLKMGR_INTER_s  ALT_CLKMGR_INTER_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_INTER register from the beginning of the component. */
#define ALT_CLKMGR_INTER_OFST        0x8

/*
 * Register : Interrupt Enable Register - intren
 * 
 * Contain fields that enable the interrupt.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                                  
 * :-------|:-------|:------|:----------------------------------------------
 *  [0]    | RW     | 0x0   | Main PLL Achieved Lock Interrupt Enable      
 *  [1]    | RW     | 0x0   | Peripheral PLL Achieved Lock Interrupt Enable
 *  [2]    | RW     | 0x0   | SDRAM PLL Achieved Lock Interrupt Enable     
 *  [3]    | RW     | 0x0   | Main PLL Achieved Lock Interrupt Enable      
 *  [4]    | RW     | 0x0   | Peripheral PLL Achieved Lock Interrupt Enable
 *  [5]    | RW     | 0x0   | SDRAM PLL Achieved Lock Interrupt Enable     
 *  [31:6] | ???    | 0x0   | *UNDEFINED*                                  
 * 
 */
/*
 * Field : Main PLL Achieved Lock Interrupt Enable - mainpllachieved
 * 
 * When set to 1, the Main PLL achieved lock bit is ORed into the Clock Manager
 * interrupt output.  When set to 0 the Main PLL achieved lock bit is not ORed into
 * the Clock Manager interrupt output.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTREN_MAINPLLACHIEVED register field. */
#define ALT_CLKMGR_INTREN_MAINPLLACHIEVED_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTREN_MAINPLLACHIEVED register field. */
#define ALT_CLKMGR_INTREN_MAINPLLACHIEVED_MSB        0
/* The width in bits of the ALT_CLKMGR_INTREN_MAINPLLACHIEVED register field. */
#define ALT_CLKMGR_INTREN_MAINPLLACHIEVED_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTREN_MAINPLLACHIEVED register field value. */
#define ALT_CLKMGR_INTREN_MAINPLLACHIEVED_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_INTREN_MAINPLLACHIEVED register field value. */
#define ALT_CLKMGR_INTREN_MAINPLLACHIEVED_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_INTREN_MAINPLLACHIEVED register field. */
#define ALT_CLKMGR_INTREN_MAINPLLACHIEVED_RESET      0x0
/* Extracts the ALT_CLKMGR_INTREN_MAINPLLACHIEVED field value from a register. */
#define ALT_CLKMGR_INTREN_MAINPLLACHIEVED_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_INTREN_MAINPLLACHIEVED register field value suitable for setting the register. */
#define ALT_CLKMGR_INTREN_MAINPLLACHIEVED_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Peripheral PLL Achieved Lock Interrupt Enable - perpllachieved
 * 
 * When set to 1, the Peripheral PLL achieved lock bit is ORed into the Clock
 * Manager interrupt output.  When set to 0 the Peripheral PLL achieved lock bit is
 * not ORed into the Clock Manager interrupt output.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTREN_PERPLLACHIEVED register field. */
#define ALT_CLKMGR_INTREN_PERPLLACHIEVED_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTREN_PERPLLACHIEVED register field. */
#define ALT_CLKMGR_INTREN_PERPLLACHIEVED_MSB        1
/* The width in bits of the ALT_CLKMGR_INTREN_PERPLLACHIEVED register field. */
#define ALT_CLKMGR_INTREN_PERPLLACHIEVED_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTREN_PERPLLACHIEVED register field value. */
#define ALT_CLKMGR_INTREN_PERPLLACHIEVED_SET_MSK    0x00000002
/* The mask used to clear the ALT_CLKMGR_INTREN_PERPLLACHIEVED register field value. */
#define ALT_CLKMGR_INTREN_PERPLLACHIEVED_CLR_MSK    0xfffffffd
/* The reset value of the ALT_CLKMGR_INTREN_PERPLLACHIEVED register field. */
#define ALT_CLKMGR_INTREN_PERPLLACHIEVED_RESET      0x0
/* Extracts the ALT_CLKMGR_INTREN_PERPLLACHIEVED field value from a register. */
#define ALT_CLKMGR_INTREN_PERPLLACHIEVED_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_CLKMGR_INTREN_PERPLLACHIEVED register field value suitable for setting the register. */
#define ALT_CLKMGR_INTREN_PERPLLACHIEVED_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : SDRAM PLL Achieved Lock Interrupt Enable - sdrpllachieved
 * 
 * When set to 1, the SDRAM PLL achieved lock bit is ORed into the Clock Manager
 * interrupt output.  When set to 0 the SDRAM PLL achieved lock bit is not ORed
 * into the Clock Manager interrupt output.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTREN_SDRPLLACHIEVED register field. */
#define ALT_CLKMGR_INTREN_SDRPLLACHIEVED_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTREN_SDRPLLACHIEVED register field. */
#define ALT_CLKMGR_INTREN_SDRPLLACHIEVED_MSB        2
/* The width in bits of the ALT_CLKMGR_INTREN_SDRPLLACHIEVED register field. */
#define ALT_CLKMGR_INTREN_SDRPLLACHIEVED_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTREN_SDRPLLACHIEVED register field value. */
#define ALT_CLKMGR_INTREN_SDRPLLACHIEVED_SET_MSK    0x00000004
/* The mask used to clear the ALT_CLKMGR_INTREN_SDRPLLACHIEVED register field value. */
#define ALT_CLKMGR_INTREN_SDRPLLACHIEVED_CLR_MSK    0xfffffffb
/* The reset value of the ALT_CLKMGR_INTREN_SDRPLLACHIEVED register field. */
#define ALT_CLKMGR_INTREN_SDRPLLACHIEVED_RESET      0x0
/* Extracts the ALT_CLKMGR_INTREN_SDRPLLACHIEVED field value from a register. */
#define ALT_CLKMGR_INTREN_SDRPLLACHIEVED_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_CLKMGR_INTREN_SDRPLLACHIEVED register field value suitable for setting the register. */
#define ALT_CLKMGR_INTREN_SDRPLLACHIEVED_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Main PLL Achieved Lock Interrupt Enable - mainplllost
 * 
 * When set to 1, the Main PLL lost lock bit is ORed into the Clock Manager
 * interrupt output.  When set to 0 the Main PLL lost lock bit is not ORed into the
 * Clock Manager interrupt output.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTREN_MAINPLLLOST register field. */
#define ALT_CLKMGR_INTREN_MAINPLLLOST_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTREN_MAINPLLLOST register field. */
#define ALT_CLKMGR_INTREN_MAINPLLLOST_MSB        3
/* The width in bits of the ALT_CLKMGR_INTREN_MAINPLLLOST register field. */
#define ALT_CLKMGR_INTREN_MAINPLLLOST_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTREN_MAINPLLLOST register field value. */
#define ALT_CLKMGR_INTREN_MAINPLLLOST_SET_MSK    0x00000008
/* The mask used to clear the ALT_CLKMGR_INTREN_MAINPLLLOST register field value. */
#define ALT_CLKMGR_INTREN_MAINPLLLOST_CLR_MSK    0xfffffff7
/* The reset value of the ALT_CLKMGR_INTREN_MAINPLLLOST register field. */
#define ALT_CLKMGR_INTREN_MAINPLLLOST_RESET      0x0
/* Extracts the ALT_CLKMGR_INTREN_MAINPLLLOST field value from a register. */
#define ALT_CLKMGR_INTREN_MAINPLLLOST_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_CLKMGR_INTREN_MAINPLLLOST register field value suitable for setting the register. */
#define ALT_CLKMGR_INTREN_MAINPLLLOST_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Peripheral PLL Achieved Lock Interrupt Enable - perplllost
 * 
 * When set to 1, the Peripheral PLL lost lock bit is ORed into the Clock Manager
 * interrupt output.  When set to 0 the Peripheral PLL lost lock bit is not ORed
 * into the Clock Manager interrupt output.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTREN_PERPLLLOST register field. */
#define ALT_CLKMGR_INTREN_PERPLLLOST_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTREN_PERPLLLOST register field. */
#define ALT_CLKMGR_INTREN_PERPLLLOST_MSB        4
/* The width in bits of the ALT_CLKMGR_INTREN_PERPLLLOST register field. */
#define ALT_CLKMGR_INTREN_PERPLLLOST_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTREN_PERPLLLOST register field value. */
#define ALT_CLKMGR_INTREN_PERPLLLOST_SET_MSK    0x00000010
/* The mask used to clear the ALT_CLKMGR_INTREN_PERPLLLOST register field value. */
#define ALT_CLKMGR_INTREN_PERPLLLOST_CLR_MSK    0xffffffef
/* The reset value of the ALT_CLKMGR_INTREN_PERPLLLOST register field. */
#define ALT_CLKMGR_INTREN_PERPLLLOST_RESET      0x0
/* Extracts the ALT_CLKMGR_INTREN_PERPLLLOST field value from a register. */
#define ALT_CLKMGR_INTREN_PERPLLLOST_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_CLKMGR_INTREN_PERPLLLOST register field value suitable for setting the register. */
#define ALT_CLKMGR_INTREN_PERPLLLOST_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : SDRAM PLL Achieved Lock Interrupt Enable - sdrplllost
 * 
 * When set to 1, the SDRAM PLL lost lock bit is ORed into the Clock Manager
 * interrupt output.  When set to 0 the SDRAM PLL lost lock bit is not ORed into
 * the Clock Manager interrupt output.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_INTREN_SDRPLLLOST register field. */
#define ALT_CLKMGR_INTREN_SDRPLLLOST_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_INTREN_SDRPLLLOST register field. */
#define ALT_CLKMGR_INTREN_SDRPLLLOST_MSB        5
/* The width in bits of the ALT_CLKMGR_INTREN_SDRPLLLOST register field. */
#define ALT_CLKMGR_INTREN_SDRPLLLOST_WIDTH      1
/* The mask used to set the ALT_CLKMGR_INTREN_SDRPLLLOST register field value. */
#define ALT_CLKMGR_INTREN_SDRPLLLOST_SET_MSK    0x00000020
/* The mask used to clear the ALT_CLKMGR_INTREN_SDRPLLLOST register field value. */
#define ALT_CLKMGR_INTREN_SDRPLLLOST_CLR_MSK    0xffffffdf
/* The reset value of the ALT_CLKMGR_INTREN_SDRPLLLOST register field. */
#define ALT_CLKMGR_INTREN_SDRPLLLOST_RESET      0x0
/* Extracts the ALT_CLKMGR_INTREN_SDRPLLLOST field value from a register. */
#define ALT_CLKMGR_INTREN_SDRPLLLOST_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_CLKMGR_INTREN_SDRPLLLOST register field value suitable for setting the register. */
#define ALT_CLKMGR_INTREN_SDRPLLLOST_SET(value) (((value) << 5) & 0x00000020)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_INTREN.
 */
struct ALT_CLKMGR_INTREN_s
{
    uint32_t  mainpllachieved :  1;  /* Main PLL Achieved Lock Interrupt Enable */
    uint32_t  perpllachieved  :  1;  /* Peripheral PLL Achieved Lock Interrupt Enable */
    uint32_t  sdrpllachieved  :  1;  /* SDRAM PLL Achieved Lock Interrupt Enable */
    uint32_t  mainplllost     :  1;  /* Main PLL Achieved Lock Interrupt Enable */
    uint32_t  perplllost      :  1;  /* Peripheral PLL Achieved Lock Interrupt Enable */
    uint32_t  sdrplllost      :  1;  /* SDRAM PLL Achieved Lock Interrupt Enable */
    uint32_t                  : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_INTREN. */
typedef volatile struct ALT_CLKMGR_INTREN_s  ALT_CLKMGR_INTREN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_INTREN register from the beginning of the component. */
#define ALT_CLKMGR_INTREN_OFST        0xc

/*
 * Register : Debug clock Control Register - dbctrl
 * 
 * Contains fields that control the debug clocks.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                   
 * :-------|:-------|:------|:-------------------------------
 *  [0]    | RW     | 0x1   | Debug Clocks Stay on EOSC1_CLK
 *  [1]    | RW     | 0x1   | Debug Clocks Enable Safe Mode 
 *  [31:2] | ???    | 0x0   | *UNDEFINED*                   
 * 
 */
/*
 * Field : Debug Clocks Stay on EOSC1_CLK - stayosc1
 * 
 * When this bit is set the debug root clock (Main PLL C2 output) will always be
 * bypassed to the EOSC1_clk independent of any other clock manager settings.
 * When clear the debug source will be a function of register settings in the clock
 * manager.  Clocks affected by this bit are dbg_at_clk, dbg_clk, dbg_trace_clk,
 * and dbg_timer_clk.
 * 
 * The reset value for this bit is applied on a cold reset.   Warm reset has no
 * affect on this bit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_DBCTL_STAYOSC1 register field. */
#define ALT_CLKMGR_DBCTL_STAYOSC1_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_DBCTL_STAYOSC1 register field. */
#define ALT_CLKMGR_DBCTL_STAYOSC1_MSB        0
/* The width in bits of the ALT_CLKMGR_DBCTL_STAYOSC1 register field. */
#define ALT_CLKMGR_DBCTL_STAYOSC1_WIDTH      1
/* The mask used to set the ALT_CLKMGR_DBCTL_STAYOSC1 register field value. */
#define ALT_CLKMGR_DBCTL_STAYOSC1_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_DBCTL_STAYOSC1 register field value. */
#define ALT_CLKMGR_DBCTL_STAYOSC1_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_DBCTL_STAYOSC1 register field. */
#define ALT_CLKMGR_DBCTL_STAYOSC1_RESET      0x1
/* Extracts the ALT_CLKMGR_DBCTL_STAYOSC1 field value from a register. */
#define ALT_CLKMGR_DBCTL_STAYOSC1_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_DBCTL_STAYOSC1 register field value suitable for setting the register. */
#define ALT_CLKMGR_DBCTL_STAYOSC1_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Debug Clocks Enable Safe Mode - ensfmdwr
 * 
 * When this bit is set the debug clocks will be affected by the assertion of Safe
 * Mode on a warm reset if Stay OSC1 is not set.
 * 
 * When this bit is clear the debug clocks will not be affected by the assertion of
 * Safe Mode on a warm reset.
 * 
 * If Debug Clocks are in Safe Mode they are taken out of Safe Mode when the Safe
 * Mode bit is cleared independent of this bit.The reset value of this bit is
 * applied on a cold reset; warm reset has no affect on this bit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_DBCTL_ENSFMDWR register field. */
#define ALT_CLKMGR_DBCTL_ENSFMDWR_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_DBCTL_ENSFMDWR register field. */
#define ALT_CLKMGR_DBCTL_ENSFMDWR_MSB        1
/* The width in bits of the ALT_CLKMGR_DBCTL_ENSFMDWR register field. */
#define ALT_CLKMGR_DBCTL_ENSFMDWR_WIDTH      1
/* The mask used to set the ALT_CLKMGR_DBCTL_ENSFMDWR register field value. */
#define ALT_CLKMGR_DBCTL_ENSFMDWR_SET_MSK    0x00000002
/* The mask used to clear the ALT_CLKMGR_DBCTL_ENSFMDWR register field value. */
#define ALT_CLKMGR_DBCTL_ENSFMDWR_CLR_MSK    0xfffffffd
/* The reset value of the ALT_CLKMGR_DBCTL_ENSFMDWR register field. */
#define ALT_CLKMGR_DBCTL_ENSFMDWR_RESET      0x1
/* Extracts the ALT_CLKMGR_DBCTL_ENSFMDWR field value from a register. */
#define ALT_CLKMGR_DBCTL_ENSFMDWR_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_CLKMGR_DBCTL_ENSFMDWR register field value suitable for setting the register. */
#define ALT_CLKMGR_DBCTL_ENSFMDWR_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_DBCTL.
 */
struct ALT_CLKMGR_DBCTL_s
{
    uint32_t  stayosc1 :  1;  /* Debug Clocks Stay on EOSC1_CLK */
    uint32_t  ensfmdwr :  1;  /* Debug Clocks Enable Safe Mode */
    uint32_t           : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_DBCTL. */
typedef volatile struct ALT_CLKMGR_DBCTL_s  ALT_CLKMGR_DBCTL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_DBCTL register from the beginning of the component. */
#define ALT_CLKMGR_DBCTL_OFST        0x10

/*
 * Register : Status Register - stat
 * 
 * Provides status of Hardware Managed Clock transition State Machine.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description           
 * :-------|:-------|:------|:-----------------------
 *  [0]    | R      | 0x0   | HW Managed Clocks BUSY
 *  [31:1] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : HW Managed Clocks BUSY - busy
 * 
 * This read only bit indicates that the Hardware Managed clock's state machine is
 * active.  If the state machine is active, then the clocks are in transition.
 * Software should poll this bit after changing the source of internal clocks when
 * writing to the BYPASS, CTRL or DBCTRL registers.   Immediately following writes
 * to any of these registers, SW should wait until this bit is IDLE before
 * proceeding with any other register writes in the Clock Manager.
 * 
 * The reset value of this bit is applied on a cold reset; warm reset has no affect
 * on this bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description         
 * :----------------------------|:------|:---------------------
 *  ALT_CLKMGR_STAT_BUSY_E_IDLE | 0x0   | Clocks stable       
 *  ALT_CLKMGR_STAT_BUSY_E_BUSY | 0x1   | Clocks in transition
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_STAT_BUSY
 * 
 * Clocks stable
 */
#define ALT_CLKMGR_STAT_BUSY_E_IDLE 0x0
/*
 * Enumerated value for register field ALT_CLKMGR_STAT_BUSY
 * 
 * Clocks in transition
 */
#define ALT_CLKMGR_STAT_BUSY_E_BUSY 0x1

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_STAT_BUSY register field. */
#define ALT_CLKMGR_STAT_BUSY_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_STAT_BUSY register field. */
#define ALT_CLKMGR_STAT_BUSY_MSB        0
/* The width in bits of the ALT_CLKMGR_STAT_BUSY register field. */
#define ALT_CLKMGR_STAT_BUSY_WIDTH      1
/* The mask used to set the ALT_CLKMGR_STAT_BUSY register field value. */
#define ALT_CLKMGR_STAT_BUSY_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_STAT_BUSY register field value. */
#define ALT_CLKMGR_STAT_BUSY_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_STAT_BUSY register field. */
#define ALT_CLKMGR_STAT_BUSY_RESET      0x0
/* Extracts the ALT_CLKMGR_STAT_BUSY field value from a register. */
#define ALT_CLKMGR_STAT_BUSY_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_STAT_BUSY register field value suitable for setting the register. */
#define ALT_CLKMGR_STAT_BUSY_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_STAT.
 */
struct ALT_CLKMGR_STAT_s
{
    const uint32_t  busy :  1;  /* HW Managed Clocks BUSY */
    uint32_t             : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_STAT. */
typedef volatile struct ALT_CLKMGR_STAT_s  ALT_CLKMGR_STAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_STAT register from the beginning of the component. */
#define ALT_CLKMGR_STAT_OFST        0x14

/*
 * Register Group : Main PLL Group - ALT_CLKMGR_MAINPLL
 * Main PLL Group
 * 
 * Contains registers with settings for the Main PLL.
 * 
 */
/*
 * Register : Main PLL VCO Control Register - vco
 * 
 * Contains settings that control the Main PLL VCO. The VCO output frequency is the
 * input frequency multiplied by the numerator (M+1) and divided by the denominator
 * (N+1). The VCO input clock source is always eosc1_clk.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                    
 * :--------|:-------|:------|:--------------------------------
 *  [0]     | RW     | 0x1   | BG PWRDN                       
 *  [1]     | RW     | 0x0   | Enable                         
 *  [2]     | RW     | 0x1   | Power down                     
 *  [15:3]  | RW     | 0x1   | Numerator (M)                  
 *  [21:16] | RW     | 0x1   | Denominator (N)                
 *  [23:22] | ???    | 0x0   | *UNDEFINED*                    
 *  [24]    | RW     | 0x0   | All Output Counter Reset       
 *  [30:25] | RW     | 0x0   | Output Counter Reset           
 *  [31]    | RW     | 0x1   | External Regulator Input Select
 * 
 */
/*
 * Field : BG PWRDN - bgpwrdn
 * 
 * If '1', powers down bandgap. If '0', bandgap is not power down.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_VCO_BGPWRDN register field. */
#define ALT_CLKMGR_MAINPLL_VCO_BGPWRDN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_VCO_BGPWRDN register field. */
#define ALT_CLKMGR_MAINPLL_VCO_BGPWRDN_MSB        0
/* The width in bits of the ALT_CLKMGR_MAINPLL_VCO_BGPWRDN register field. */
#define ALT_CLKMGR_MAINPLL_VCO_BGPWRDN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_VCO_BGPWRDN register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_BGPWRDN_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_MAINPLL_VCO_BGPWRDN register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_BGPWRDN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_MAINPLL_VCO_BGPWRDN register field. */
#define ALT_CLKMGR_MAINPLL_VCO_BGPWRDN_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_VCO_BGPWRDN field value from a register. */
#define ALT_CLKMGR_MAINPLL_VCO_BGPWRDN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_MAINPLL_VCO_BGPWRDN register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_VCO_BGPWRDN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Enable - en
 * 
 * If '1', VCO is enabled. If '0', VCO is in reset.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_VCO_EN register field. */
#define ALT_CLKMGR_MAINPLL_VCO_EN_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_VCO_EN register field. */
#define ALT_CLKMGR_MAINPLL_VCO_EN_MSB        1
/* The width in bits of the ALT_CLKMGR_MAINPLL_VCO_EN register field. */
#define ALT_CLKMGR_MAINPLL_VCO_EN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_VCO_EN register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_EN_SET_MSK    0x00000002
/* The mask used to clear the ALT_CLKMGR_MAINPLL_VCO_EN register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_EN_CLR_MSK    0xfffffffd
/* The reset value of the ALT_CLKMGR_MAINPLL_VCO_EN register field. */
#define ALT_CLKMGR_MAINPLL_VCO_EN_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_VCO_EN field value from a register. */
#define ALT_CLKMGR_MAINPLL_VCO_EN_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_CLKMGR_MAINPLL_VCO_EN register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_VCO_EN_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Power down - pwrdn
 * 
 * If '1', power down analog circuitry. If '0', analog circuitry not powered down.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_VCO_PWRDN register field. */
#define ALT_CLKMGR_MAINPLL_VCO_PWRDN_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_VCO_PWRDN register field. */
#define ALT_CLKMGR_MAINPLL_VCO_PWRDN_MSB        2
/* The width in bits of the ALT_CLKMGR_MAINPLL_VCO_PWRDN register field. */
#define ALT_CLKMGR_MAINPLL_VCO_PWRDN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_VCO_PWRDN register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_PWRDN_SET_MSK    0x00000004
/* The mask used to clear the ALT_CLKMGR_MAINPLL_VCO_PWRDN register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_PWRDN_CLR_MSK    0xfffffffb
/* The reset value of the ALT_CLKMGR_MAINPLL_VCO_PWRDN register field. */
#define ALT_CLKMGR_MAINPLL_VCO_PWRDN_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_VCO_PWRDN field value from a register. */
#define ALT_CLKMGR_MAINPLL_VCO_PWRDN_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_CLKMGR_MAINPLL_VCO_PWRDN register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_VCO_PWRDN_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Numerator (M) - numer
 * 
 * Numerator in VCO output frequency equation. For incremental frequency change, if
 * the new value lead to less than 20% of the frequency change, this value can be
 * changed without resetting the PLL. The Numerator and Denominator can not be
 * changed at the same time for incremental frequency changed.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_VCO_NUMER register field. */
#define ALT_CLKMGR_MAINPLL_VCO_NUMER_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_VCO_NUMER register field. */
#define ALT_CLKMGR_MAINPLL_VCO_NUMER_MSB        15
/* The width in bits of the ALT_CLKMGR_MAINPLL_VCO_NUMER register field. */
#define ALT_CLKMGR_MAINPLL_VCO_NUMER_WIDTH      13
/* The mask used to set the ALT_CLKMGR_MAINPLL_VCO_NUMER register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_NUMER_SET_MSK    0x0000fff8
/* The mask used to clear the ALT_CLKMGR_MAINPLL_VCO_NUMER register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_NUMER_CLR_MSK    0xffff0007
/* The reset value of the ALT_CLKMGR_MAINPLL_VCO_NUMER register field. */
#define ALT_CLKMGR_MAINPLL_VCO_NUMER_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_VCO_NUMER field value from a register. */
#define ALT_CLKMGR_MAINPLL_VCO_NUMER_GET(value) (((value) & 0x0000fff8) >> 3)
/* Produces a ALT_CLKMGR_MAINPLL_VCO_NUMER register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_VCO_NUMER_SET(value) (((value) << 3) & 0x0000fff8)

/*
 * Field : Denominator (N) - denom
 * 
 * Denominator in VCO output frequency equation. For incremental frequency change,
 * if the new value lead to less than 20% of the frequency change, this value can
 * be changed without resetting the PLL. The Numerator and Denominator can not be
 * changed at the same time for incremental frequency changed.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_VCO_DENOM register field. */
#define ALT_CLKMGR_MAINPLL_VCO_DENOM_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_VCO_DENOM register field. */
#define ALT_CLKMGR_MAINPLL_VCO_DENOM_MSB        21
/* The width in bits of the ALT_CLKMGR_MAINPLL_VCO_DENOM register field. */
#define ALT_CLKMGR_MAINPLL_VCO_DENOM_WIDTH      6
/* The mask used to set the ALT_CLKMGR_MAINPLL_VCO_DENOM register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_DENOM_SET_MSK    0x003f0000
/* The mask used to clear the ALT_CLKMGR_MAINPLL_VCO_DENOM register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_DENOM_CLR_MSK    0xffc0ffff
/* The reset value of the ALT_CLKMGR_MAINPLL_VCO_DENOM register field. */
#define ALT_CLKMGR_MAINPLL_VCO_DENOM_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_VCO_DENOM field value from a register. */
#define ALT_CLKMGR_MAINPLL_VCO_DENOM_GET(value) (((value) & 0x003f0000) >> 16)
/* Produces a ALT_CLKMGR_MAINPLL_VCO_DENOM register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_VCO_DENOM_SET(value) (((value) << 16) & 0x003f0000)

/*
 * Field : All Output Counter Reset - outresetall
 * 
 * Before releasing Bypass, All Output Counter Reset must be set and cleared by
 * software for correct clock operation.
 * 
 * If '1', Reset phase multiplexer and all output counter state. So that after the
 * assertion all the clocks output are start from rising edge align.
 * 
 * If '0', phase multiplexer and output counter state not reset and no change to
 * the phase of the clock outputs.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL register field. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL register field. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL_MSB        24
/* The width in bits of the ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL register field. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL_SET_MSK    0x01000000
/* The mask used to clear the ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL_CLR_MSK    0xfeffffff
/* The reset value of the ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL register field. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL field value from a register. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL_GET(value) (((value) & 0x01000000) >> 24)
/* Produces a ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRSTALL_SET(value) (((value) << 24) & 0x01000000)

/*
 * Field : Output Counter Reset - outreset
 * 
 * Resets the individual PLL output counter.
 * 
 * For software to change the PLL output counter without producing glitches on the
 * respective clock, SW must set the VCO register respective Output Counter Reset
 * bit. Software then polls the respective Output Counter Reset Acknowledge bit in
 * the Output Counter Reset Ack Status Register. Software then writes the
 * appropriate counter register, and then clears the respective VCO register Output
 * Counter Reset bit.
 * 
 * LSB 'outreset[0]' corresponds to PLL output clock C0, etc.
 * 
 * If set to '1', reset output divider, no clock output from counter.
 * 
 * If set to '0', counter is not reset.
 * 
 * The reset value of this bit is applied on a cold reset; warm reset has no affect
 * on this bit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_VCO_OUTRST register field. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRST_LSB        25
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_VCO_OUTRST register field. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRST_MSB        30
/* The width in bits of the ALT_CLKMGR_MAINPLL_VCO_OUTRST register field. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRST_WIDTH      6
/* The mask used to set the ALT_CLKMGR_MAINPLL_VCO_OUTRST register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRST_SET_MSK    0x7e000000
/* The mask used to clear the ALT_CLKMGR_MAINPLL_VCO_OUTRST register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRST_CLR_MSK    0x81ffffff
/* The reset value of the ALT_CLKMGR_MAINPLL_VCO_OUTRST register field. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRST_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_VCO_OUTRST field value from a register. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRST_GET(value) (((value) & 0x7e000000) >> 25)
/* Produces a ALT_CLKMGR_MAINPLL_VCO_OUTRST register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_VCO_OUTRST_SET(value) (((value) << 25) & 0x7e000000)

/*
 * Field : External Regulator Input Select - regextsel
 * 
 * If set to '1', the external regulator is selected for the PLL.
 * 
 * If set to '0', the internal regulator is slected.
 * 
 * It is strongly recommended to select the external regulator while the PLL is not
 * enabled (in reset), and  then disable the external regulater once the PLL
 * becomes enabled.  Software should simulateously update the 'Enable' bit and the
 * 'External Regulator Input Select' in the same write access to the VCO register.
 * When the 'Enable' bit is clear, the 'External Regulator Input Select' should be
 * set, and vice versa.
 * 
 * The reset value of this bit is applied on a cold reset; warm reset has no affect
 * on this bit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL register field. */
#define ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL register field. */
#define ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL_MSB        31
/* The width in bits of the ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL register field. */
#define ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL_SET_MSK    0x80000000
/* The mask used to clear the ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL register field value. */
#define ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL_CLR_MSK    0x7fffffff
/* The reset value of the ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL register field. */
#define ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL field value from a register. */
#define ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_VCO_REGEXTSEL_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_MAINPLL_VCO.
 */
struct ALT_CLKMGR_MAINPLL_VCO_s
{
    uint32_t  bgpwrdn     :  1;  /* BG PWRDN */
    uint32_t  en          :  1;  /* Enable */
    uint32_t  pwrdn       :  1;  /* Power down */
    uint32_t  numer       : 13;  /* Numerator (M) */
    uint32_t  denom       :  6;  /* Denominator (N) */
    uint32_t              :  2;  /* *UNDEFINED* */
    uint32_t  outresetall :  1;  /* All Output Counter Reset */
    uint32_t  outreset    :  6;  /* Output Counter Reset */
    uint32_t  regextsel   :  1;  /* External Regulator Input Select */
};

/* The typedef declaration for register ALT_CLKMGR_MAINPLL_VCO. */
typedef volatile struct ALT_CLKMGR_MAINPLL_VCO_s  ALT_CLKMGR_MAINPLL_VCO_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_MAINPLL_VCO register from the beginning of the component. */
#define ALT_CLKMGR_MAINPLL_VCO_OFST        0x0

/*
 * Register : Main PLL VCO Advanced Control Register - misc
 * 
 * Contains VCO control signals and other PLL control signals need to be
 * controllable through register.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                  
 * :--------|:-------|:------|:------------------------------
 *  [0]     | RW     | 0x0   | Loop Bandwidth Adjust Enabled
 *  [12:1]  | RW     | 0x1   | Loop Bandwidth Adjust        
 *  [13]    | RW     | 0x0   | Fast Locking Enable          
 *  [14]    | RW     | 0x1   | Saturation Enable            
 *  [31:15] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : Loop Bandwidth Adjust Enabled - bwadjen
 * 
 * If set to 1, the Loop Bandwidth Adjust value comes from the Loop Bandwidth
 * Adjust field.
 * 
 * If set to 0, the Loop Bandwidth Adjust value equals the M field divided by 2
 * value of the VCO Control Register.  The M divided by 2 is the upper 12 bits
 * (12:1) of the M field in the VCO register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_MISC_BWADJEN register field. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJEN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_MISC_BWADJEN register field. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJEN_MSB        0
/* The width in bits of the ALT_CLKMGR_MAINPLL_MISC_BWADJEN register field. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJEN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_MISC_BWADJEN register field value. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJEN_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_MAINPLL_MISC_BWADJEN register field value. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJEN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_MAINPLL_MISC_BWADJEN register field. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJEN_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_MISC_BWADJEN field value from a register. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJEN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_MAINPLL_MISC_BWADJEN register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJEN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Loop Bandwidth Adjust - bwadj
 * 
 * Provides Loop Bandwidth Adjust value.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_MISC_BWADJ register field. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJ_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_MISC_BWADJ register field. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJ_MSB        12
/* The width in bits of the ALT_CLKMGR_MAINPLL_MISC_BWADJ register field. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJ_WIDTH      12
/* The mask used to set the ALT_CLKMGR_MAINPLL_MISC_BWADJ register field value. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJ_SET_MSK    0x00001ffe
/* The mask used to clear the ALT_CLKMGR_MAINPLL_MISC_BWADJ register field value. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJ_CLR_MSK    0xffffe001
/* The reset value of the ALT_CLKMGR_MAINPLL_MISC_BWADJ register field. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJ_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_MISC_BWADJ field value from a register. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJ_GET(value) (((value) & 0x00001ffe) >> 1)
/* Produces a ALT_CLKMGR_MAINPLL_MISC_BWADJ register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_MISC_BWADJ_SET(value) (((value) << 1) & 0x00001ffe)

/*
 * Field : Fast Locking Enable - fasten
 * 
 * Enables fast locking circuit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_MISC_FASTEN register field. */
#define ALT_CLKMGR_MAINPLL_MISC_FASTEN_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_MISC_FASTEN register field. */
#define ALT_CLKMGR_MAINPLL_MISC_FASTEN_MSB        13
/* The width in bits of the ALT_CLKMGR_MAINPLL_MISC_FASTEN register field. */
#define ALT_CLKMGR_MAINPLL_MISC_FASTEN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_MISC_FASTEN register field value. */
#define ALT_CLKMGR_MAINPLL_MISC_FASTEN_SET_MSK    0x00002000
/* The mask used to clear the ALT_CLKMGR_MAINPLL_MISC_FASTEN register field value. */
#define ALT_CLKMGR_MAINPLL_MISC_FASTEN_CLR_MSK    0xffffdfff
/* The reset value of the ALT_CLKMGR_MAINPLL_MISC_FASTEN register field. */
#define ALT_CLKMGR_MAINPLL_MISC_FASTEN_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_MISC_FASTEN field value from a register. */
#define ALT_CLKMGR_MAINPLL_MISC_FASTEN_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_CLKMGR_MAINPLL_MISC_FASTEN register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_MISC_FASTEN_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : Saturation Enable - saten
 * 
 * Enables saturation behavior.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_MISC_SATEN register field. */
#define ALT_CLKMGR_MAINPLL_MISC_SATEN_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_MISC_SATEN register field. */
#define ALT_CLKMGR_MAINPLL_MISC_SATEN_MSB        14
/* The width in bits of the ALT_CLKMGR_MAINPLL_MISC_SATEN register field. */
#define ALT_CLKMGR_MAINPLL_MISC_SATEN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_MISC_SATEN register field value. */
#define ALT_CLKMGR_MAINPLL_MISC_SATEN_SET_MSK    0x00004000
/* The mask used to clear the ALT_CLKMGR_MAINPLL_MISC_SATEN register field value. */
#define ALT_CLKMGR_MAINPLL_MISC_SATEN_CLR_MSK    0xffffbfff
/* The reset value of the ALT_CLKMGR_MAINPLL_MISC_SATEN register field. */
#define ALT_CLKMGR_MAINPLL_MISC_SATEN_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_MISC_SATEN field value from a register. */
#define ALT_CLKMGR_MAINPLL_MISC_SATEN_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_CLKMGR_MAINPLL_MISC_SATEN register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_MISC_SATEN_SET(value) (((value) << 14) & 0x00004000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_MAINPLL_MISC.
 */
struct ALT_CLKMGR_MAINPLL_MISC_s
{
    uint32_t  bwadjen :  1;  /* Loop Bandwidth Adjust Enabled */
    uint32_t  bwadj   : 12;  /* Loop Bandwidth Adjust */
    uint32_t  fasten  :  1;  /* Fast Locking Enable */
    uint32_t  saten   :  1;  /* Saturation Enable */
    uint32_t          : 17;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_MAINPLL_MISC. */
typedef volatile struct ALT_CLKMGR_MAINPLL_MISC_s  ALT_CLKMGR_MAINPLL_MISC_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_MAINPLL_MISC register from the beginning of the component. */
#define ALT_CLKMGR_MAINPLL_MISC_OFST        0x4

/*
 * Register : Main PLL C0 Control Register for Clock mpu_clk - mpuclk
 * 
 * Contains settings that control clock mpu_clk generated from the C0 output of the
 * Main PLL.
 * 
 * Only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [8:0]  | RW     | 0x0   | Counter    
 *  [31:9] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO/2 frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_MPUCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MPUCLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_MPUCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MPUCLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_MAINPLL_MPUCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MPUCLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_MAINPLL_MPUCLK_CNT register field value. */
#define ALT_CLKMGR_MAINPLL_MPUCLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_MAINPLL_MPUCLK_CNT register field value. */
#define ALT_CLKMGR_MAINPLL_MPUCLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_MAINPLL_MPUCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MPUCLK_CNT_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_MPUCLK_CNT field value from a register. */
#define ALT_CLKMGR_MAINPLL_MPUCLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_MAINPLL_MPUCLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_MPUCLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_MAINPLL_MPUCLK.
 */
struct ALT_CLKMGR_MAINPLL_MPUCLK_s
{
    uint32_t  cnt :  9;  /* Counter */
    uint32_t      : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_MAINPLL_MPUCLK. */
typedef volatile struct ALT_CLKMGR_MAINPLL_MPUCLK_s  ALT_CLKMGR_MAINPLL_MPUCLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_MAINPLL_MPUCLK register from the beginning of the component. */
#define ALT_CLKMGR_MAINPLL_MPUCLK_OFST        0x8

/*
 * Register : Main PLL C1 Control Register for Clock main_clk - mainclk
 * 
 * Contains settings that control clock main_clk generated from the C1 output of
 * the Main PLL.
 * 
 * Only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [8:0]  | RW     | 0x0   | Counter    
 *  [31:9] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO/4 frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_MAINCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MAINCLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_MAINCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MAINCLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_MAINPLL_MAINCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MAINCLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_MAINPLL_MAINCLK_CNT register field value. */
#define ALT_CLKMGR_MAINPLL_MAINCLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_MAINPLL_MAINCLK_CNT register field value. */
#define ALT_CLKMGR_MAINPLL_MAINCLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_MAINPLL_MAINCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MAINCLK_CNT_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_MAINCLK_CNT field value from a register. */
#define ALT_CLKMGR_MAINPLL_MAINCLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_MAINPLL_MAINCLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_MAINCLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_MAINPLL_MAINCLK.
 */
struct ALT_CLKMGR_MAINPLL_MAINCLK_s
{
    uint32_t  cnt :  9;  /* Counter */
    uint32_t      : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_MAINPLL_MAINCLK. */
typedef volatile struct ALT_CLKMGR_MAINPLL_MAINCLK_s  ALT_CLKMGR_MAINPLL_MAINCLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_MAINPLL_MAINCLK register from the beginning of the component. */
#define ALT_CLKMGR_MAINPLL_MAINCLK_OFST        0xc

/*
 * Register : Main PLL C2 Control Register for Clock dbg_base_clk - dbgatclk
 * 
 * Contains settings that control clock dbg_base_clk generated from the C2 output
 * of the Main PLL.
 * 
 * Only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [8:0]  | RW     | 0x0   | Counter    
 *  [31:9] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO/4 frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_DBGATCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_DBGATCLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_DBGATCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_DBGATCLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_MAINPLL_DBGATCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_DBGATCLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_MAINPLL_DBGATCLK_CNT register field value. */
#define ALT_CLKMGR_MAINPLL_DBGATCLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_MAINPLL_DBGATCLK_CNT register field value. */
#define ALT_CLKMGR_MAINPLL_DBGATCLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_MAINPLL_DBGATCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_DBGATCLK_CNT_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_DBGATCLK_CNT field value from a register. */
#define ALT_CLKMGR_MAINPLL_DBGATCLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_MAINPLL_DBGATCLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_DBGATCLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_MAINPLL_DBGATCLK.
 */
struct ALT_CLKMGR_MAINPLL_DBGATCLK_s
{
    uint32_t  cnt :  9;  /* Counter */
    uint32_t      : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_MAINPLL_DBGATCLK. */
typedef volatile struct ALT_CLKMGR_MAINPLL_DBGATCLK_s  ALT_CLKMGR_MAINPLL_DBGATCLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_MAINPLL_DBGATCLK register from the beginning of the component. */
#define ALT_CLKMGR_MAINPLL_DBGATCLK_OFST        0x10

/*
 * Register : Main PLL C3 Control Register for Clock main_qspi_clk - mainqspiclk
 * 
 * Contains settings that control clock main_qspi_clk generated from the C3 output
 * of the Main PLL.
 * 
 * Only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [8:0]  | RW     | 0x3   | Counter    
 *  [31:9] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT register field value. */
#define ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT register field value. */
#define ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT_RESET      0x3
/* Extracts the ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT field value from a register. */
#define ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_MAINQSPICLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_MAINPLL_MAINQSPICLK.
 */
struct ALT_CLKMGR_MAINPLL_MAINQSPICLK_s
{
    uint32_t  cnt :  9;  /* Counter */
    uint32_t      : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_MAINPLL_MAINQSPICLK. */
typedef volatile struct ALT_CLKMGR_MAINPLL_MAINQSPICLK_s  ALT_CLKMGR_MAINPLL_MAINQSPICLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_MAINPLL_MAINQSPICLK register from the beginning of the component. */
#define ALT_CLKMGR_MAINPLL_MAINQSPICLK_OFST        0x14

/*
 * Register : Main PLL C4 Control Register for Clock main_nand_sdmmc_clk - mainnandsdmmcclk
 * 
 * Contains settings that control clock main_nand_sdmmc_clk generated from the C4
 * output of the Main PLL.
 * 
 * Only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [8:0]  | RW     | 0x3   | Counter    
 *  [31:9] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT register field value. */
#define ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT register field value. */
#define ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT_RESET      0x3
/* Extracts the ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT field value from a register. */
#define ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK.
 */
struct ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_s
{
    uint32_t  cnt :  9;  /* Counter */
    uint32_t      : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK. */
typedef volatile struct ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_s  ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK register from the beginning of the component. */
#define ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_OFST        0x18

/*
 * Register : Main PLL C5 Control Register for Clock cfg_s2f_user0_clk - cfgs2fuser0clk
 * 
 * Contains settings that control clock cfg_s2f_user0_clk generated from the C5
 * output of the Main PLL.
 * 
 * Qsys and user documenation refer to cfg_s2f_user0_clk as cfg_h2f_user0_clk.
 * 
 * Only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [8:0]  | RW     | 0xf   | Counter    
 *  [31:9] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT register field value. */
#define ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT register field value. */
#define ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT register field. */
#define ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT_RESET      0xf
/* Extracts the ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT field value from a register. */
#define ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK.
 */
struct ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_s
{
    uint32_t  cnt :  9;  /* Counter */
    uint32_t      : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK. */
typedef volatile struct ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_s  ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK register from the beginning of the component. */
#define ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_OFST        0x1c

/*
 * Register : Enable Register - en
 * 
 * Contains fields that control clock enables for clocks derived from the Main PLL.
 * 
 * 1: The clock is enabled.
 * 
 * 0: The clock is disabled.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description         
 * :--------|:-------|:------|:---------------------
 *  [0]     | RW     | 0x1   | l4_main_clk Enable  
 *  [1]     | RW     | 0x1   | l3_mp_clk Enable    
 *  [2]     | RW     | 0x1   | l4_mp_clk Enable    
 *  [3]     | RW     | 0x1   | l4_sp_clk Enable    
 *  [4]     | RW     | 0x1   | dbg_at_clk Enable   
 *  [5]     | RW     | 0x1   | dbg_clk Enable      
 *  [6]     | RW     | 0x1   | dbg_trace_clk Enable
 *  [7]     | RW     | 0x1   | dbg_timer_clk Enable
 *  [8]     | RW     | 0x1   | cfg_clk Enable      
 *  [9]     | RW     | 0x1   | s2f_user0_clk Enable
 *  [31:10] | ???    | 0x0   | *UNDEFINED*         
 * 
 */
/*
 * Field : l4_main_clk Enable - l4mainclk
 * 
 * Enables clock l4_main_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_EN_L4MAINCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L4MAINCLK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_EN_L4MAINCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L4MAINCLK_MSB        0
/* The width in bits of the ALT_CLKMGR_MAINPLL_EN_L4MAINCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L4MAINCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_EN_L4MAINCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_L4MAINCLK_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_MAINPLL_EN_L4MAINCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_L4MAINCLK_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_MAINPLL_EN_L4MAINCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L4MAINCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_EN_L4MAINCLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_EN_L4MAINCLK_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_MAINPLL_EN_L4MAINCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_EN_L4MAINCLK_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : l3_mp_clk Enable - l3mpclk
 * 
 * Enables clock l3_mp_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_EN_L3MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L3MPCLK_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_EN_L3MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L3MPCLK_MSB        1
/* The width in bits of the ALT_CLKMGR_MAINPLL_EN_L3MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L3MPCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_EN_L3MPCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_L3MPCLK_SET_MSK    0x00000002
/* The mask used to clear the ALT_CLKMGR_MAINPLL_EN_L3MPCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_L3MPCLK_CLR_MSK    0xfffffffd
/* The reset value of the ALT_CLKMGR_MAINPLL_EN_L3MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L3MPCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_EN_L3MPCLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_EN_L3MPCLK_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_CLKMGR_MAINPLL_EN_L3MPCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_EN_L3MPCLK_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : l4_mp_clk Enable - l4mpclk
 * 
 * Enables clock l4_mp_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_EN_L4MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L4MPCLK_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_EN_L4MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L4MPCLK_MSB        2
/* The width in bits of the ALT_CLKMGR_MAINPLL_EN_L4MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L4MPCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_EN_L4MPCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_L4MPCLK_SET_MSK    0x00000004
/* The mask used to clear the ALT_CLKMGR_MAINPLL_EN_L4MPCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_L4MPCLK_CLR_MSK    0xfffffffb
/* The reset value of the ALT_CLKMGR_MAINPLL_EN_L4MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L4MPCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_EN_L4MPCLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_EN_L4MPCLK_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_CLKMGR_MAINPLL_EN_L4MPCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_EN_L4MPCLK_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : l4_sp_clk Enable - l4spclk
 * 
 * Enables clock l4_sp_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_EN_L4SPCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L4SPCLK_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_EN_L4SPCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L4SPCLK_MSB        3
/* The width in bits of the ALT_CLKMGR_MAINPLL_EN_L4SPCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L4SPCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_EN_L4SPCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_L4SPCLK_SET_MSK    0x00000008
/* The mask used to clear the ALT_CLKMGR_MAINPLL_EN_L4SPCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_L4SPCLK_CLR_MSK    0xfffffff7
/* The reset value of the ALT_CLKMGR_MAINPLL_EN_L4SPCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_L4SPCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_EN_L4SPCLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_EN_L4SPCLK_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_CLKMGR_MAINPLL_EN_L4SPCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_EN_L4SPCLK_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : dbg_at_clk Enable - dbgatclk
 * 
 * Enables clock dbg_at_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_EN_DBGATCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGATCLK_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_EN_DBGATCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGATCLK_MSB        4
/* The width in bits of the ALT_CLKMGR_MAINPLL_EN_DBGATCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGATCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_EN_DBGATCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_DBGATCLK_SET_MSK    0x00000010
/* The mask used to clear the ALT_CLKMGR_MAINPLL_EN_DBGATCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_DBGATCLK_CLR_MSK    0xffffffef
/* The reset value of the ALT_CLKMGR_MAINPLL_EN_DBGATCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGATCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_EN_DBGATCLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_EN_DBGATCLK_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_CLKMGR_MAINPLL_EN_DBGATCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_EN_DBGATCLK_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : dbg_clk Enable - dbgclk
 * 
 * Enables clock dbg_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_EN_DBGCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGCLK_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_EN_DBGCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGCLK_MSB        5
/* The width in bits of the ALT_CLKMGR_MAINPLL_EN_DBGCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_EN_DBGCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_DBGCLK_SET_MSK    0x00000020
/* The mask used to clear the ALT_CLKMGR_MAINPLL_EN_DBGCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_DBGCLK_CLR_MSK    0xffffffdf
/* The reset value of the ALT_CLKMGR_MAINPLL_EN_DBGCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_EN_DBGCLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_EN_DBGCLK_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_CLKMGR_MAINPLL_EN_DBGCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_EN_DBGCLK_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : dbg_trace_clk Enable - dbgtraceclk
 * 
 * Enables clock dbg_trace_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK_MSB        6
/* The width in bits of the ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK_SET_MSK    0x00000040
/* The mask used to clear the ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK_CLR_MSK    0xffffffbf
/* The reset value of the ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTRACECLK_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : dbg_timer_clk Enable - dbgtimerclk
 * 
 * Enables clock dbg_timer_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK_MSB        7
/* The width in bits of the ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK_SET_MSK    0x00000080
/* The mask used to clear the ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK_CLR_MSK    0xffffff7f
/* The reset value of the ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_EN_DBGTMRCLK_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : cfg_clk Enable - cfgclk
 * 
 * Enables clock cfg_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_EN_CFGCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_CFGCLK_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_EN_CFGCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_CFGCLK_MSB        8
/* The width in bits of the ALT_CLKMGR_MAINPLL_EN_CFGCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_CFGCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_EN_CFGCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_CFGCLK_SET_MSK    0x00000100
/* The mask used to clear the ALT_CLKMGR_MAINPLL_EN_CFGCLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_CFGCLK_CLR_MSK    0xfffffeff
/* The reset value of the ALT_CLKMGR_MAINPLL_EN_CFGCLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_CFGCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_EN_CFGCLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_EN_CFGCLK_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_CLKMGR_MAINPLL_EN_CFGCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_EN_CFGCLK_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : s2f_user0_clk Enable - s2fuser0clk
 * 
 * Enables clock s2f_user0_clk output.
 * 
 * Qsys and user documenation refer to s2f_user0_clk as h2f_user0_clk.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK_MSB        9
/* The width in bits of the ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK_SET_MSK    0x00000200
/* The mask used to clear the ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK register field value. */
#define ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK_CLR_MSK    0xfffffdff
/* The reset value of the ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK register field. */
#define ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_EN_S2FUSER0CLK_SET(value) (((value) << 9) & 0x00000200)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_MAINPLL_EN.
 */
struct ALT_CLKMGR_MAINPLL_EN_s
{
    uint32_t  l4mainclk   :  1;  /* l4_main_clk Enable */
    uint32_t  l3mpclk     :  1;  /* l3_mp_clk Enable */
    uint32_t  l4mpclk     :  1;  /* l4_mp_clk Enable */
    uint32_t  l4spclk     :  1;  /* l4_sp_clk Enable */
    uint32_t  dbgatclk    :  1;  /* dbg_at_clk Enable */
    uint32_t  dbgclk      :  1;  /* dbg_clk Enable */
    uint32_t  dbgtraceclk :  1;  /* dbg_trace_clk Enable */
    uint32_t  dbgtimerclk :  1;  /* dbg_timer_clk Enable */
    uint32_t  cfgclk      :  1;  /* cfg_clk Enable */
    uint32_t  s2fuser0clk :  1;  /* s2f_user0_clk Enable */
    uint32_t              : 22;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_MAINPLL_EN. */
typedef volatile struct ALT_CLKMGR_MAINPLL_EN_s  ALT_CLKMGR_MAINPLL_EN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_MAINPLL_EN register from the beginning of the component. */
#define ALT_CLKMGR_MAINPLL_EN_OFST        0x20

/*
 * Register : Main Divide Register - maindiv
 * 
 * Contains fields that control clock dividers for main clocks derived from the
 * Main PLL
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description        
 * :--------|:-------|:------|:--------------------
 *  [1:0]   | RW     | 0x0   | L3 MP Clock Divider
 *  [3:2]   | RW     | 0x0   | L3 SP Clock Divider
 *  [6:4]   | RW     | 0x0   | L4 MP Clock Divider
 *  [9:7]   | RW     | 0x0   | L4 SP Clock Divider
 *  [31:10] | ???    | 0x0   | *UNDEFINED*        
 * 
 */
/*
 * Field : L3 MP Clock Divider - l3mpclk
 * 
 * The l3_mp_clk is divided down from the l3_main_clk by the value specified in
 * this field.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description
 * :------------------------------------------|:------|:------------
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_E_DIV1 | 0x0   | Divide by 1
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_E_DIV2 | 0x1   | Divide by 2
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK
 * 
 * Divide by 1
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_E_DIV1   0x0
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK
 * 
 * Divide by 2
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_E_DIV2   0x1

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_MSB        1
/* The width in bits of the ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_WIDTH      2
/* The mask used to set the ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK register field value. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_SET_MSK    0x00000003
/* The mask used to clear the ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK register field value. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_CLR_MSK    0xfffffffc
/* The reset value of the ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3MPCLK_SET(value) (((value) << 0) & 0x00000003)

/*
 * Field : L3 SP Clock Divider - l3spclk
 * 
 * The l3_sp_clk is divided down from the l3_mp_clk by the value specified in this
 * field.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description
 * :------------------------------------------|:------|:------------
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_E_DIV1 | 0x0   | Divide by 1
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_E_DIV2 | 0x1   | Divide by 2
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK
 * 
 * Divide by 1
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_E_DIV1   0x0
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK
 * 
 * Divide by 2
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_E_DIV2   0x1

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_MSB        3
/* The width in bits of the ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_WIDTH      2
/* The mask used to set the ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK register field value. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_SET_MSK    0x0000000c
/* The mask used to clear the ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK register field value. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_CLR_MSK    0xfffffff3
/* The reset value of the ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_GET(value) (((value) & 0x0000000c) >> 2)
/* Produces a ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L3SPCLK_SET(value) (((value) << 2) & 0x0000000c)

/*
 * Field : L4 MP Clock Divider - l4mpclk
 * 
 * The l4_mp_clk is divided down from the periph_base_clk by the value specified in
 * this field.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                        | Value | Description 
 * :--------------------------------------------|:------|:-------------
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV1   | 0x0   | Divide By 1 
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV2   | 0x1   | Divide By 2 
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV4   | 0x2   | Divide By 4 
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV8   | 0x3   | Divide By 8 
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV16  | 0x4   | Divide By 16
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_RSVD_1 | 0x5   | Reserved    
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_RSVD_2 | 0x6   | Reserved    
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_RSVD_3 | 0x7   | Reserved    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK
 * 
 * Divide By 1
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV1   0x0
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK
 * 
 * Divide By 2
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV2   0x1
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK
 * 
 * Divide By 4
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV4   0x2
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK
 * 
 * Divide By 8
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV8   0x3
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK
 * 
 * Divide By 16
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_DIV16  0x4
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_RSVD_1 0x5
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_RSVD_2 0x6
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_E_RSVD_3 0x7

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_MSB        6
/* The width in bits of the ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_WIDTH      3
/* The mask used to set the ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK register field value. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_SET_MSK    0x00000070
/* The mask used to clear the ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK register field value. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_CLR_MSK    0xffffff8f
/* The reset value of the ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_GET(value) (((value) & 0x00000070) >> 4)
/* Produces a ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4MPCLK_SET(value) (((value) << 4) & 0x00000070)

/*
 * Field : L4 SP Clock Divider - l4spclk
 * 
 * The l4_sp_clk is divided down from the periph_base_clk by the value specified in
 * this field.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                        | Value | Description 
 * :--------------------------------------------|:------|:-------------
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV1   | 0x0   | Divide By 1 
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV2   | 0x1   | Divide By 2 
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV4   | 0x2   | Divide By 4 
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV8   | 0x3   | Divide By 8 
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV16  | 0x4   | Divide By 16
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_RSVD_1 | 0x5   | Reserved    
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_RSVD_2 | 0x6   | Reserved    
 *  ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_RSVD_3 | 0x7   | Reserved    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK
 * 
 * Divide By 1
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV1   0x0
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK
 * 
 * Divide By 2
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV2   0x1
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK
 * 
 * Divide By 4
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV4   0x2
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK
 * 
 * Divide By 8
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV8   0x3
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK
 * 
 * Divide By 16
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_DIV16  0x4
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_RSVD_1 0x5
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_RSVD_2 0x6
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_E_RSVD_3 0x7

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_MSB        9
/* The width in bits of the ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_WIDTH      3
/* The mask used to set the ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK register field value. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_SET_MSK    0x00000380
/* The mask used to clear the ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK register field value. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_CLR_MSK    0xfffffc7f
/* The reset value of the ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK register field. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_GET(value) (((value) & 0x00000380) >> 7)
/* Produces a ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_L4SPCLK_SET(value) (((value) << 7) & 0x00000380)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_MAINPLL_MAINDIV.
 */
struct ALT_CLKMGR_MAINPLL_MAINDIV_s
{
    uint32_t  l3mpclk :  2;  /* L3 MP Clock Divider */
    uint32_t  l3spclk :  2;  /* L3 SP Clock Divider */
    uint32_t  l4mpclk :  3;  /* L4 MP Clock Divider */
    uint32_t  l4spclk :  3;  /* L4 SP Clock Divider */
    uint32_t          : 22;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_MAINPLL_MAINDIV. */
typedef volatile struct ALT_CLKMGR_MAINPLL_MAINDIV_s  ALT_CLKMGR_MAINPLL_MAINDIV_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_MAINPLL_MAINDIV register from the beginning of the component. */
#define ALT_CLKMGR_MAINPLL_MAINDIV_OFST        0x24

/*
 * Register : Debug Divide Register - dbgdiv
 * 
 * Contains fields that control clock dividers for debug clocks derived from the
 * Main PLL
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description           
 * :-------|:-------|:------|:-----------------------
 *  [1:0]  | RW     | 0x0   | Debug AT Clock Divider
 *  [3:2]  | RW     | 0x1   | Debug Clock Divider   
 *  [31:4] | ???    | 0x0   | *UNDEFINED*           
 * 
 */
/*
 * Field : Debug AT Clock Divider - dbgatclk
 * 
 * The dbg_at_clk is divided down from the C2 output of  the Main PLL by the value
 * specified in this field.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description
 * :------------------------------------------|:------|:------------
 *  ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_E_DIV1 | 0x0   | Divide by 1
 *  ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_E_DIV2 | 0x1   | Divide by 2
 *  ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_E_DIV4 | 0x2   | Divide by 4
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK
 * 
 * Divide by 1
 */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_E_DIV1   0x0
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK
 * 
 * Divide by 2
 */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_E_DIV2   0x1
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK
 * 
 * Divide by 4
 */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_E_DIV4   0x2

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK register field. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK register field. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_MSB        1
/* The width in bits of the ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK register field. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_WIDTH      2
/* The mask used to set the ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK register field value. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_SET_MSK    0x00000003
/* The mask used to clear the ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK register field value. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_CLR_MSK    0xfffffffc
/* The reset value of the ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK register field. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGATCLK_SET(value) (((value) << 0) & 0x00000003)

/*
 * Field : Debug Clock Divider - dbgclk
 * 
 * The dbg_clk is divided down from the dbg_at_clk by the value specified in this
 * field.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                    | Value | Description
 * :----------------------------------------|:------|:------------
 *  ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_E_DIV2 | 0x1   | Divide by 2
 *  ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_E_DIV4 | 0x2   | Divide by 4
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK
 * 
 * Divide by 2
 */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_E_DIV2 0x1
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK
 * 
 * Divide by 4
 */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_E_DIV4 0x2

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK register field. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK register field. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_MSB        3
/* The width in bits of the ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK register field. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_WIDTH      2
/* The mask used to set the ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK register field value. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_SET_MSK    0x0000000c
/* The mask used to clear the ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK register field value. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_CLR_MSK    0xfffffff3
/* The reset value of the ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK register field. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_GET(value) (((value) & 0x0000000c) >> 2)
/* Produces a ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_DBGCLK_SET(value) (((value) << 2) & 0x0000000c)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_MAINPLL_DBGDIV.
 */
struct ALT_CLKMGR_MAINPLL_DBGDIV_s
{
    uint32_t  dbgatclk :  2;  /* Debug AT Clock Divider */
    uint32_t  dbgclk   :  2;  /* Debug Clock Divider */
    uint32_t           : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_MAINPLL_DBGDIV. */
typedef volatile struct ALT_CLKMGR_MAINPLL_DBGDIV_s  ALT_CLKMGR_MAINPLL_DBGDIV_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_MAINPLL_DBGDIV register from the beginning of the component. */
#define ALT_CLKMGR_MAINPLL_DBGDIV_OFST        0x28

/*
 * Register : Debug Trace Divide Register - tracediv
 * 
 * Contains a field that controls the clock divider for the debug trace clock
 * derived from the Main PLL
 * 
 * Only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description              
 * :-------|:-------|:------|:--------------------------
 *  [2:0]  | RW     | 0x0   | Debug Trace Clock Divider
 *  [31:3] | ???    | 0x0   | *UNDEFINED*              
 * 
 */
/*
 * Field : Debug Trace Clock Divider - traceclk
 * 
 * The dbg_trace_clk is divided down from the C2 output of  the Main PLL by the
 * value specified in this field.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                          | Value | Description 
 * :----------------------------------------------|:------|:-------------
 *  ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV1   | 0x0   | Divide By 1 
 *  ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV2   | 0x1   | Divide By 2 
 *  ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV4   | 0x2   | Divide By 4 
 *  ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV8   | 0x3   | Divide By 8 
 *  ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV16  | 0x4   | Divide By 16
 *  ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_RSVD_1 | 0x5   | Reserved    
 *  ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_RSVD_2 | 0x6   | Reserved    
 *  ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_RSVD_3 | 0x7   | Reserved    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK
 * 
 * Divide By 1
 */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV1     0x0
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK
 * 
 * Divide By 2
 */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV2     0x1
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK
 * 
 * Divide By 4
 */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV4     0x2
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK
 * 
 * Divide By 8
 */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV8     0x3
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK
 * 
 * Divide By 16
 */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_DIV16    0x4
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_RSVD_1   0x5
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_RSVD_2   0x6
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_E_RSVD_3   0x7

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK register field. */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK register field. */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_MSB        2
/* The width in bits of the ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK register field. */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_WIDTH      3
/* The mask used to set the ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK register field value. */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_SET_MSK    0x00000007
/* The mask used to clear the ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK register field value. */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_CLR_MSK    0xfffffff8
/* The reset value of the ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK register field. */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK field value from a register. */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_GET(value) (((value) & 0x00000007) >> 0)
/* Produces a ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_TRACECLK_SET(value) (((value) << 0) & 0x00000007)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_MAINPLL_TRACEDIV.
 */
struct ALT_CLKMGR_MAINPLL_TRACEDIV_s
{
    uint32_t  traceclk :  3;  /* Debug Trace Clock Divider */
    uint32_t           : 29;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_MAINPLL_TRACEDIV. */
typedef volatile struct ALT_CLKMGR_MAINPLL_TRACEDIV_s  ALT_CLKMGR_MAINPLL_TRACEDIV_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_MAINPLL_TRACEDIV register from the beginning of the component. */
#define ALT_CLKMGR_MAINPLL_TRACEDIV_OFST        0x2c

/*
 * Register : L4 MP SP APB Clock Source - l4src
 * 
 * Contains fields that select the clock source for L4 MP and SP APB interconnect
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description     
 * :-------|:-------|:------|:-----------------
 *  [0]    | RW     | 0x0   | l4_mp_clk Source
 *  [1]    | RW     | 0x0   | l4_sp_clk Source
 *  [31:2] | ???    | 0x0   | *UNDEFINED*     
 * 
 */
/*
 * Field : l4_mp_clk Source - l4mp
 * 
 * Selects the source for l4_mp_clk
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description    
 * :------------------------------------------|:------|:----------------
 *  ALT_CLKMGR_MAINPLL_L4SRC_L4MP_E_MAINPLL   | 0x0   | main_clk       
 *  ALT_CLKMGR_MAINPLL_L4SRC_L4MP_E_PERIPHPLL | 0x1   | periph_base_clk
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_L4SRC_L4MP
 * 
 * main_clk
 */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4MP_E_MAINPLL     0x0
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_L4SRC_L4MP
 * 
 * periph_base_clk
 */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4MP_E_PERIPHPLL   0x1

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_L4SRC_L4MP register field. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4MP_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_L4SRC_L4MP register field. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4MP_MSB        0
/* The width in bits of the ALT_CLKMGR_MAINPLL_L4SRC_L4MP register field. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4MP_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_L4SRC_L4MP register field value. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4MP_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_MAINPLL_L4SRC_L4MP register field value. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4MP_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_MAINPLL_L4SRC_L4MP register field. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4MP_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_L4SRC_L4MP field value from a register. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4MP_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_MAINPLL_L4SRC_L4MP register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4MP_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : l4_sp_clk Source - l4sp
 * 
 * Selects the source for l4_sp_clk
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                      | Value | Description    
 * :------------------------------------------|:------|:----------------
 *  ALT_CLKMGR_MAINPLL_L4SRC_L4SP_E_MAINPLL   | 0x0   | main_clk       
 *  ALT_CLKMGR_MAINPLL_L4SRC_L4SP_E_PERIPHPLL | 0x1   | periph_base_clk
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_L4SRC_L4SP
 * 
 * main_clk
 */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4SP_E_MAINPLL     0x0
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_L4SRC_L4SP
 * 
 * periph_base_clk
 */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4SP_E_PERIPHPLL   0x1

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_L4SRC_L4SP register field. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4SP_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_L4SRC_L4SP register field. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4SP_MSB        1
/* The width in bits of the ALT_CLKMGR_MAINPLL_L4SRC_L4SP register field. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4SP_WIDTH      1
/* The mask used to set the ALT_CLKMGR_MAINPLL_L4SRC_L4SP register field value. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4SP_SET_MSK    0x00000002
/* The mask used to clear the ALT_CLKMGR_MAINPLL_L4SRC_L4SP register field value. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4SP_CLR_MSK    0xfffffffd
/* The reset value of the ALT_CLKMGR_MAINPLL_L4SRC_L4SP register field. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4SP_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_L4SRC_L4SP field value from a register. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4SP_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_CLKMGR_MAINPLL_L4SRC_L4SP register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_L4SRC_L4SP_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_MAINPLL_L4SRC.
 */
struct ALT_CLKMGR_MAINPLL_L4SRC_s
{
    uint32_t  l4mp :  1;  /* l4_mp_clk Source */
    uint32_t  l4sp :  1;  /* l4_sp_clk Source */
    uint32_t       : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_MAINPLL_L4SRC. */
typedef volatile struct ALT_CLKMGR_MAINPLL_L4SRC_s  ALT_CLKMGR_MAINPLL_L4SRC_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_MAINPLL_L4SRC register from the beginning of the component. */
#define ALT_CLKMGR_MAINPLL_L4SRC_OFST        0x30

/*
 * Register : Main PLL Output Counter Reset Ack Status Register - stat
 * 
 * Contains Output Clock Counter Reset acknowledge status.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                     
 * :-------|:-------|:------|:---------------------------------
 *  [5:0]  | R      | 0x0   | Output Counter Reset Acknowledge
 *  [31:6] | ???    | 0x0   | *UNDEFINED*                     
 * 
 */
/*
 * Field : Output Counter Reset Acknowledge - outresetack
 * 
 * These read only bits per PLL output indicate that the PLL has received the
 * Output Reset Counter request and has gracefully stopped the respective PLL
 * output clock.
 * 
 * For software to change the PLL output counter without producing glitches on the
 * respective clock, SW must set the VCO register respective Output Counter Reset
 * bit. Software then polls the respective Output Counter Reset Acknowledge bit in
 * the Output Counter Reset Ack Status Register. Software then writes the
 * appropriate counter register, and then clears the respective VCO register Output
 * Counter Reset bit.
 * 
 * The reset value of this bit is applied on a cold reset; warm reset has no affect
 * on this bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                        | Value | Description                         
 * :--------------------------------------------|:------|:-------------------------------------
 *  ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK_E_IDLE    | 0x0   | Idle                                
 *  ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK_E_ACK_RXD | 0x1   | Output Counter Acknowledge received.
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK
 * 
 * Idle
 */
#define ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK_E_IDLE    0x0
/*
 * Enumerated value for register field ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK
 * 
 * Output Counter Acknowledge received.
 */
#define ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK_E_ACK_RXD 0x1

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK register field. */
#define ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK register field. */
#define ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK_MSB        5
/* The width in bits of the ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK register field. */
#define ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK_WIDTH      6
/* The mask used to set the ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK register field value. */
#define ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK_SET_MSK    0x0000003f
/* The mask used to clear the ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK register field value. */
#define ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK_CLR_MSK    0xffffffc0
/* The reset value of the ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK register field. */
#define ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK_RESET      0x0
/* Extracts the ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK field value from a register. */
#define ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK_GET(value) (((value) & 0x0000003f) >> 0)
/* Produces a ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK register field value suitable for setting the register. */
#define ALT_CLKMGR_MAINPLL_STAT_OUTRSTACK_SET(value) (((value) << 0) & 0x0000003f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_MAINPLL_STAT.
 */
struct ALT_CLKMGR_MAINPLL_STAT_s
{
    const uint32_t  outresetack :  6;  /* Output Counter Reset Acknowledge */
    uint32_t                    : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_MAINPLL_STAT. */
typedef volatile struct ALT_CLKMGR_MAINPLL_STAT_s  ALT_CLKMGR_MAINPLL_STAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_MAINPLL_STAT register from the beginning of the component. */
#define ALT_CLKMGR_MAINPLL_STAT_OFST        0x34

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_CLKMGR_MAINPLL.
 */
struct ALT_CLKMGR_MAINPLL_s
{
    volatile ALT_CLKMGR_MAINPLL_VCO_t               vco;                /* ALT_CLKMGR_MAINPLL_VCO */
    volatile ALT_CLKMGR_MAINPLL_MISC_t              misc;               /* ALT_CLKMGR_MAINPLL_MISC */
    volatile ALT_CLKMGR_MAINPLL_MPUCLK_t            mpuclk;             /* ALT_CLKMGR_MAINPLL_MPUCLK */
    volatile ALT_CLKMGR_MAINPLL_MAINCLK_t           mainclk;            /* ALT_CLKMGR_MAINPLL_MAINCLK */
    volatile ALT_CLKMGR_MAINPLL_DBGATCLK_t          dbgatclk;           /* ALT_CLKMGR_MAINPLL_DBGATCLK */
    volatile ALT_CLKMGR_MAINPLL_MAINQSPICLK_t       mainqspiclk;        /* ALT_CLKMGR_MAINPLL_MAINQSPICLK */
    volatile ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK_t  mainnandsdmmcclk;   /* ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK */
    volatile ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK_t    cfgs2fuser0clk;     /* ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK */
    volatile ALT_CLKMGR_MAINPLL_EN_t                en;                 /* ALT_CLKMGR_MAINPLL_EN */
    volatile ALT_CLKMGR_MAINPLL_MAINDIV_t           maindiv;            /* ALT_CLKMGR_MAINPLL_MAINDIV */
    volatile ALT_CLKMGR_MAINPLL_DBGDIV_t            dbgdiv;             /* ALT_CLKMGR_MAINPLL_DBGDIV */
    volatile ALT_CLKMGR_MAINPLL_TRACEDIV_t          tracediv;           /* ALT_CLKMGR_MAINPLL_TRACEDIV */
    volatile ALT_CLKMGR_MAINPLL_L4SRC_t             l4src;              /* ALT_CLKMGR_MAINPLL_L4SRC */
    volatile ALT_CLKMGR_MAINPLL_STAT_t              stat;               /* ALT_CLKMGR_MAINPLL_STAT */
    volatile uint32_t                               _pad_0x38_0x40[2];  /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_CLKMGR_MAINPLL. */
typedef volatile struct ALT_CLKMGR_MAINPLL_s  ALT_CLKMGR_MAINPLL_t;
/* The struct declaration for the raw register contents of register group ALT_CLKMGR_MAINPLL. */
struct ALT_CLKMGR_MAINPLL_raw_s
{
    volatile uint32_t  vco;                /* ALT_CLKMGR_MAINPLL_VCO */
    volatile uint32_t  misc;               /* ALT_CLKMGR_MAINPLL_MISC */
    volatile uint32_t  mpuclk;             /* ALT_CLKMGR_MAINPLL_MPUCLK */
    volatile uint32_t  mainclk;            /* ALT_CLKMGR_MAINPLL_MAINCLK */
    volatile uint32_t  dbgatclk;           /* ALT_CLKMGR_MAINPLL_DBGATCLK */
    volatile uint32_t  mainqspiclk;        /* ALT_CLKMGR_MAINPLL_MAINQSPICLK */
    volatile uint32_t  mainnandsdmmcclk;   /* ALT_CLKMGR_MAINPLL_MAINNANDSDMMCCLK */
    volatile uint32_t  cfgs2fuser0clk;     /* ALT_CLKMGR_MAINPLL_CFGS2FUSER0CLK */
    volatile uint32_t  en;                 /* ALT_CLKMGR_MAINPLL_EN */
    volatile uint32_t  maindiv;            /* ALT_CLKMGR_MAINPLL_MAINDIV */
    volatile uint32_t  dbgdiv;             /* ALT_CLKMGR_MAINPLL_DBGDIV */
    volatile uint32_t  tracediv;           /* ALT_CLKMGR_MAINPLL_TRACEDIV */
    volatile uint32_t  l4src;              /* ALT_CLKMGR_MAINPLL_L4SRC */
    volatile uint32_t  stat;               /* ALT_CLKMGR_MAINPLL_STAT */
    volatile uint32_t  _pad_0x38_0x40[2];  /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_CLKMGR_MAINPLL. */
typedef volatile struct ALT_CLKMGR_MAINPLL_raw_s  ALT_CLKMGR_MAINPLL_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : Peripheral PLL Group - ALT_CLKMGR_PERPLL
 * Peripheral PLL Group
 * 
 * Contains registers with settings for the Peripheral PLL.
 * 
 */
/*
 * Register : Peripheral PLL VCO Control Register - vco
 * 
 * Contains settings that control the Peripheral PLL VCO. The VCO output frequency
 * is the input frequency multiplied by the numerator (M+1) and divided by the
 * denominator (N+1).
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                    
 * :--------|:-------|:------|:--------------------------------
 *  [0]     | RW     | 0x1   | BG PWRDN                       
 *  [1]     | RW     | 0x0   | Enable                         
 *  [2]     | RW     | 0x1   | Power down                     
 *  [15:3]  | RW     | 0x1   | Numerator (M)                  
 *  [21:16] | RW     | 0x1   | Denominator (N)                
 *  [23:22] | RW     | 0x0   | Clock Source                   
 *  [24]    | RW     | 0x0   | All Output Counter Reset       
 *  [30:25] | RW     | 0x0   | Output Counter Reset           
 *  [31]    | RW     | 0x1   | External Regulator Input Select
 * 
 */
/*
 * Field : BG PWRDN - bgpwrdn
 * 
 * If '1', powers down bandgap. If '0', bandgap is not power down.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_VCO_BGPWRDN register field. */
#define ALT_CLKMGR_PERPLL_VCO_BGPWRDN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_VCO_BGPWRDN register field. */
#define ALT_CLKMGR_PERPLL_VCO_BGPWRDN_MSB        0
/* The width in bits of the ALT_CLKMGR_PERPLL_VCO_BGPWRDN register field. */
#define ALT_CLKMGR_PERPLL_VCO_BGPWRDN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_VCO_BGPWRDN register field value. */
#define ALT_CLKMGR_PERPLL_VCO_BGPWRDN_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_PERPLL_VCO_BGPWRDN register field value. */
#define ALT_CLKMGR_PERPLL_VCO_BGPWRDN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_PERPLL_VCO_BGPWRDN register field. */
#define ALT_CLKMGR_PERPLL_VCO_BGPWRDN_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_VCO_BGPWRDN field value from a register. */
#define ALT_CLKMGR_PERPLL_VCO_BGPWRDN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_PERPLL_VCO_BGPWRDN register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_VCO_BGPWRDN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Enable - en
 * 
 * If '1', VCO is enabled. If '0', VCO is in reset.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_VCO_EN register field. */
#define ALT_CLKMGR_PERPLL_VCO_EN_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_VCO_EN register field. */
#define ALT_CLKMGR_PERPLL_VCO_EN_MSB        1
/* The width in bits of the ALT_CLKMGR_PERPLL_VCO_EN register field. */
#define ALT_CLKMGR_PERPLL_VCO_EN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_VCO_EN register field value. */
#define ALT_CLKMGR_PERPLL_VCO_EN_SET_MSK    0x00000002
/* The mask used to clear the ALT_CLKMGR_PERPLL_VCO_EN register field value. */
#define ALT_CLKMGR_PERPLL_VCO_EN_CLR_MSK    0xfffffffd
/* The reset value of the ALT_CLKMGR_PERPLL_VCO_EN register field. */
#define ALT_CLKMGR_PERPLL_VCO_EN_RESET      0x0
/* Extracts the ALT_CLKMGR_PERPLL_VCO_EN field value from a register. */
#define ALT_CLKMGR_PERPLL_VCO_EN_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_CLKMGR_PERPLL_VCO_EN register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_VCO_EN_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Power down - pwrdn
 * 
 * If '1', power down analog circuitry. If '0', analog circuitry not powered down.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_VCO_PWRDN register field. */
#define ALT_CLKMGR_PERPLL_VCO_PWRDN_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_VCO_PWRDN register field. */
#define ALT_CLKMGR_PERPLL_VCO_PWRDN_MSB        2
/* The width in bits of the ALT_CLKMGR_PERPLL_VCO_PWRDN register field. */
#define ALT_CLKMGR_PERPLL_VCO_PWRDN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_VCO_PWRDN register field value. */
#define ALT_CLKMGR_PERPLL_VCO_PWRDN_SET_MSK    0x00000004
/* The mask used to clear the ALT_CLKMGR_PERPLL_VCO_PWRDN register field value. */
#define ALT_CLKMGR_PERPLL_VCO_PWRDN_CLR_MSK    0xfffffffb
/* The reset value of the ALT_CLKMGR_PERPLL_VCO_PWRDN register field. */
#define ALT_CLKMGR_PERPLL_VCO_PWRDN_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_VCO_PWRDN field value from a register. */
#define ALT_CLKMGR_PERPLL_VCO_PWRDN_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_CLKMGR_PERPLL_VCO_PWRDN register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_VCO_PWRDN_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Numerator (M) - numer
 * 
 * Numerator in VCO output frequency equation. For incremental frequency change, if
 * the new value lead to less than 20% of the frequency change, this value can be
 * changed without resetting the PLL. The Numerator and Denominator can not be
 * changed at the same time for incremental frequency changed.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_VCO_NUMER register field. */
#define ALT_CLKMGR_PERPLL_VCO_NUMER_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_VCO_NUMER register field. */
#define ALT_CLKMGR_PERPLL_VCO_NUMER_MSB        15
/* The width in bits of the ALT_CLKMGR_PERPLL_VCO_NUMER register field. */
#define ALT_CLKMGR_PERPLL_VCO_NUMER_WIDTH      13
/* The mask used to set the ALT_CLKMGR_PERPLL_VCO_NUMER register field value. */
#define ALT_CLKMGR_PERPLL_VCO_NUMER_SET_MSK    0x0000fff8
/* The mask used to clear the ALT_CLKMGR_PERPLL_VCO_NUMER register field value. */
#define ALT_CLKMGR_PERPLL_VCO_NUMER_CLR_MSK    0xffff0007
/* The reset value of the ALT_CLKMGR_PERPLL_VCO_NUMER register field. */
#define ALT_CLKMGR_PERPLL_VCO_NUMER_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_VCO_NUMER field value from a register. */
#define ALT_CLKMGR_PERPLL_VCO_NUMER_GET(value) (((value) & 0x0000fff8) >> 3)
/* Produces a ALT_CLKMGR_PERPLL_VCO_NUMER register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_VCO_NUMER_SET(value) (((value) << 3) & 0x0000fff8)

/*
 * Field : Denominator (N) - denom
 * 
 * Denominator in VCO output frequency equation. For incremental frequency change,
 * if the new value lead to less than 20% of the frequency change, this value can
 * be changed without resetting the PLL. The Numerator and Denominator can not be
 * changed at the same time for incremental frequency changed.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_VCO_DENOM register field. */
#define ALT_CLKMGR_PERPLL_VCO_DENOM_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_VCO_DENOM register field. */
#define ALT_CLKMGR_PERPLL_VCO_DENOM_MSB        21
/* The width in bits of the ALT_CLKMGR_PERPLL_VCO_DENOM register field. */
#define ALT_CLKMGR_PERPLL_VCO_DENOM_WIDTH      6
/* The mask used to set the ALT_CLKMGR_PERPLL_VCO_DENOM register field value. */
#define ALT_CLKMGR_PERPLL_VCO_DENOM_SET_MSK    0x003f0000
/* The mask used to clear the ALT_CLKMGR_PERPLL_VCO_DENOM register field value. */
#define ALT_CLKMGR_PERPLL_VCO_DENOM_CLR_MSK    0xffc0ffff
/* The reset value of the ALT_CLKMGR_PERPLL_VCO_DENOM register field. */
#define ALT_CLKMGR_PERPLL_VCO_DENOM_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_VCO_DENOM field value from a register. */
#define ALT_CLKMGR_PERPLL_VCO_DENOM_GET(value) (((value) & 0x003f0000) >> 16)
/* Produces a ALT_CLKMGR_PERPLL_VCO_DENOM register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_VCO_DENOM_SET(value) (((value) << 16) & 0x003f0000)

/*
 * Field : Clock Source - psrc
 * 
 * Controls the VCO input clock source.
 * 
 * Qsys and user documenation refer to f2s_periph_ref_clk as f2h_periph_ref_clk.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                        | Value | Description       
 * :--------------------------------------------|:------|:-------------------
 *  ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC1          | 0x0   | eosc1_clk         
 *  ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC2          | 0x1   | eosc2_clk         
 *  ALT_CLKMGR_PERPLL_VCO_PSRC_E_F2S_PERIPH_REF | 0x2   | f2s_periph_ref_clk
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_VCO_PSRC
 * 
 * eosc1_clk
 */
#define ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC1          0x0
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_VCO_PSRC
 * 
 * eosc2_clk
 */
#define ALT_CLKMGR_PERPLL_VCO_PSRC_E_EOSC2          0x1
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_VCO_PSRC
 * 
 * f2s_periph_ref_clk
 */
#define ALT_CLKMGR_PERPLL_VCO_PSRC_E_F2S_PERIPH_REF 0x2

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_VCO_PSRC register field. */
#define ALT_CLKMGR_PERPLL_VCO_PSRC_LSB        22
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_VCO_PSRC register field. */
#define ALT_CLKMGR_PERPLL_VCO_PSRC_MSB        23
/* The width in bits of the ALT_CLKMGR_PERPLL_VCO_PSRC register field. */
#define ALT_CLKMGR_PERPLL_VCO_PSRC_WIDTH      2
/* The mask used to set the ALT_CLKMGR_PERPLL_VCO_PSRC register field value. */
#define ALT_CLKMGR_PERPLL_VCO_PSRC_SET_MSK    0x00c00000
/* The mask used to clear the ALT_CLKMGR_PERPLL_VCO_PSRC register field value. */
#define ALT_CLKMGR_PERPLL_VCO_PSRC_CLR_MSK    0xff3fffff
/* The reset value of the ALT_CLKMGR_PERPLL_VCO_PSRC register field. */
#define ALT_CLKMGR_PERPLL_VCO_PSRC_RESET      0x0
/* Extracts the ALT_CLKMGR_PERPLL_VCO_PSRC field value from a register. */
#define ALT_CLKMGR_PERPLL_VCO_PSRC_GET(value) (((value) & 0x00c00000) >> 22)
/* Produces a ALT_CLKMGR_PERPLL_VCO_PSRC register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_VCO_PSRC_SET(value) (((value) << 22) & 0x00c00000)

/*
 * Field : All Output Counter Reset - outresetall
 * 
 * Before releasing Bypass, All Output Counter Reset must be set and cleared by
 * software for correct clock operation.
 * 
 * If '1', Reset phase multiplexer and all output counter state. So that after the
 * assertion all the clocks output are start from rising edge align.
 * 
 * If '0', phase multiplexer and output counter state not reset and no change to
 * the phase of the clock outputs.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_VCO_OUTRSTALL register field. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRSTALL_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_VCO_OUTRSTALL register field. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRSTALL_MSB        24
/* The width in bits of the ALT_CLKMGR_PERPLL_VCO_OUTRSTALL register field. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRSTALL_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_VCO_OUTRSTALL register field value. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRSTALL_SET_MSK    0x01000000
/* The mask used to clear the ALT_CLKMGR_PERPLL_VCO_OUTRSTALL register field value. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRSTALL_CLR_MSK    0xfeffffff
/* The reset value of the ALT_CLKMGR_PERPLL_VCO_OUTRSTALL register field. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRSTALL_RESET      0x0
/* Extracts the ALT_CLKMGR_PERPLL_VCO_OUTRSTALL field value from a register. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRSTALL_GET(value) (((value) & 0x01000000) >> 24)
/* Produces a ALT_CLKMGR_PERPLL_VCO_OUTRSTALL register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRSTALL_SET(value) (((value) << 24) & 0x01000000)

/*
 * Field : Output Counter Reset - outreset
 * 
 * Resets the individual PLL output counter.
 * 
 * For software to change the PLL output counter without producing glitches on the
 * respective clock, SW must set the VCO register respective Output Counter Reset
 * bit. Software then polls the respective Output Counter Reset Acknowledge bit in
 * the Output Counter Reset Ack Status Register. Software then writes the
 * appropriate counter register, and then clears the respective VCO register Output
 * Counter Reset bit.
 * 
 * LSB 'outreset[0]' corresponds to PLL output clock C0, etc.
 * 
 * If set to '1', reset output divider, no clock output from counter.
 * 
 * If set to '0', counter is not reset.
 * 
 * The reset value of this bit is applied on a cold reset; warm reset has no affect
 * on this bit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_VCO_OUTRST register field. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRST_LSB        25
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_VCO_OUTRST register field. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRST_MSB        30
/* The width in bits of the ALT_CLKMGR_PERPLL_VCO_OUTRST register field. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRST_WIDTH      6
/* The mask used to set the ALT_CLKMGR_PERPLL_VCO_OUTRST register field value. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRST_SET_MSK    0x7e000000
/* The mask used to clear the ALT_CLKMGR_PERPLL_VCO_OUTRST register field value. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRST_CLR_MSK    0x81ffffff
/* The reset value of the ALT_CLKMGR_PERPLL_VCO_OUTRST register field. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRST_RESET      0x0
/* Extracts the ALT_CLKMGR_PERPLL_VCO_OUTRST field value from a register. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRST_GET(value) (((value) & 0x7e000000) >> 25)
/* Produces a ALT_CLKMGR_PERPLL_VCO_OUTRST register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_VCO_OUTRST_SET(value) (((value) << 25) & 0x7e000000)

/*
 * Field : External Regulator Input Select - regextsel
 * 
 * If set to '1', the external regulator is selected for the PLL.
 * 
 * If set to '0', the internal regulator is slected.
 * 
 * It is strongly recommended to select the external regulator while the PLL is not
 * enabled (in reset), and  then disable the external regulater once the PLL
 * becomes enabled.  Software should simulateously update the 'Enable' bit and the
 * 'External Regulator Input Select' in the same write access to the VCO register.
 * When the 'Enable' bit is clear, the 'External Regulator Input Select' should be
 * set, and vice versa.
 * 
 * The reset value of this bit is applied on a cold reset; warm reset has no affect
 * on this bit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_VCO_REGEXTSEL register field. */
#define ALT_CLKMGR_PERPLL_VCO_REGEXTSEL_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_VCO_REGEXTSEL register field. */
#define ALT_CLKMGR_PERPLL_VCO_REGEXTSEL_MSB        31
/* The width in bits of the ALT_CLKMGR_PERPLL_VCO_REGEXTSEL register field. */
#define ALT_CLKMGR_PERPLL_VCO_REGEXTSEL_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_VCO_REGEXTSEL register field value. */
#define ALT_CLKMGR_PERPLL_VCO_REGEXTSEL_SET_MSK    0x80000000
/* The mask used to clear the ALT_CLKMGR_PERPLL_VCO_REGEXTSEL register field value. */
#define ALT_CLKMGR_PERPLL_VCO_REGEXTSEL_CLR_MSK    0x7fffffff
/* The reset value of the ALT_CLKMGR_PERPLL_VCO_REGEXTSEL register field. */
#define ALT_CLKMGR_PERPLL_VCO_REGEXTSEL_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_VCO_REGEXTSEL field value from a register. */
#define ALT_CLKMGR_PERPLL_VCO_REGEXTSEL_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_CLKMGR_PERPLL_VCO_REGEXTSEL register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_VCO_REGEXTSEL_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_PERPLL_VCO.
 */
struct ALT_CLKMGR_PERPLL_VCO_s
{
    uint32_t  bgpwrdn     :  1;  /* BG PWRDN */
    uint32_t  en          :  1;  /* Enable */
    uint32_t  pwrdn       :  1;  /* Power down */
    uint32_t  numer       : 13;  /* Numerator (M) */
    uint32_t  denom       :  6;  /* Denominator (N) */
    uint32_t  psrc        :  2;  /* Clock Source */
    uint32_t  outresetall :  1;  /* All Output Counter Reset */
    uint32_t  outreset    :  6;  /* Output Counter Reset */
    uint32_t  regextsel   :  1;  /* External Regulator Input Select */
};

/* The typedef declaration for register ALT_CLKMGR_PERPLL_VCO. */
typedef volatile struct ALT_CLKMGR_PERPLL_VCO_s  ALT_CLKMGR_PERPLL_VCO_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_PERPLL_VCO register from the beginning of the component. */
#define ALT_CLKMGR_PERPLL_VCO_OFST        0x0

/*
 * Register : Peripheral PLL VCO Advanced Control Register - misc
 * 
 * Contains VCO control signals and other PLL control signals need to be
 * controllable through register.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                  
 * :--------|:-------|:------|:------------------------------
 *  [0]     | RW     | 0x0   | Loop Bandwidth Adjust Enabled
 *  [12:1]  | RW     | 0x1   | Loop Bandwidth Adjust        
 *  [13]    | RW     | 0x0   | Fast Locking Enable          
 *  [14]    | RW     | 0x1   | Saturation Enable            
 *  [31:15] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : Loop Bandwidth Adjust Enabled - bwadjen
 * 
 * If set to 1, the Loop Bandwidth Adjust value comes from the Loop Bandwidth
 * Adjust field.
 * 
 * If set to 0, the Loop Bandwidth Adjust value equals the M field divided by 2
 * value of the VCO Control Register.  The M divided by 2 is the upper 12 bits
 * (12:1) of the M field in the VCO register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_MISC_BWADJEN register field. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJEN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_MISC_BWADJEN register field. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJEN_MSB        0
/* The width in bits of the ALT_CLKMGR_PERPLL_MISC_BWADJEN register field. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJEN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_MISC_BWADJEN register field value. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJEN_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_PERPLL_MISC_BWADJEN register field value. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJEN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_PERPLL_MISC_BWADJEN register field. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJEN_RESET      0x0
/* Extracts the ALT_CLKMGR_PERPLL_MISC_BWADJEN field value from a register. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJEN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_PERPLL_MISC_BWADJEN register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJEN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Loop Bandwidth Adjust - bwadj
 * 
 * Provides Loop Bandwidth Adjust value.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_MISC_BWADJ register field. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJ_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_MISC_BWADJ register field. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJ_MSB        12
/* The width in bits of the ALT_CLKMGR_PERPLL_MISC_BWADJ register field. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJ_WIDTH      12
/* The mask used to set the ALT_CLKMGR_PERPLL_MISC_BWADJ register field value. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJ_SET_MSK    0x00001ffe
/* The mask used to clear the ALT_CLKMGR_PERPLL_MISC_BWADJ register field value. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJ_CLR_MSK    0xffffe001
/* The reset value of the ALT_CLKMGR_PERPLL_MISC_BWADJ register field. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJ_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_MISC_BWADJ field value from a register. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJ_GET(value) (((value) & 0x00001ffe) >> 1)
/* Produces a ALT_CLKMGR_PERPLL_MISC_BWADJ register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_MISC_BWADJ_SET(value) (((value) << 1) & 0x00001ffe)

/*
 * Field : Fast Locking Enable - fasten
 * 
 * Enables fast locking circuit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_MISC_FASTEN register field. */
#define ALT_CLKMGR_PERPLL_MISC_FASTEN_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_MISC_FASTEN register field. */
#define ALT_CLKMGR_PERPLL_MISC_FASTEN_MSB        13
/* The width in bits of the ALT_CLKMGR_PERPLL_MISC_FASTEN register field. */
#define ALT_CLKMGR_PERPLL_MISC_FASTEN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_MISC_FASTEN register field value. */
#define ALT_CLKMGR_PERPLL_MISC_FASTEN_SET_MSK    0x00002000
/* The mask used to clear the ALT_CLKMGR_PERPLL_MISC_FASTEN register field value. */
#define ALT_CLKMGR_PERPLL_MISC_FASTEN_CLR_MSK    0xffffdfff
/* The reset value of the ALT_CLKMGR_PERPLL_MISC_FASTEN register field. */
#define ALT_CLKMGR_PERPLL_MISC_FASTEN_RESET      0x0
/* Extracts the ALT_CLKMGR_PERPLL_MISC_FASTEN field value from a register. */
#define ALT_CLKMGR_PERPLL_MISC_FASTEN_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_CLKMGR_PERPLL_MISC_FASTEN register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_MISC_FASTEN_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : Saturation Enable - saten
 * 
 * Enables saturation behavior.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_MISC_SATEN register field. */
#define ALT_CLKMGR_PERPLL_MISC_SATEN_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_MISC_SATEN register field. */
#define ALT_CLKMGR_PERPLL_MISC_SATEN_MSB        14
/* The width in bits of the ALT_CLKMGR_PERPLL_MISC_SATEN register field. */
#define ALT_CLKMGR_PERPLL_MISC_SATEN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_MISC_SATEN register field value. */
#define ALT_CLKMGR_PERPLL_MISC_SATEN_SET_MSK    0x00004000
/* The mask used to clear the ALT_CLKMGR_PERPLL_MISC_SATEN register field value. */
#define ALT_CLKMGR_PERPLL_MISC_SATEN_CLR_MSK    0xffffbfff
/* The reset value of the ALT_CLKMGR_PERPLL_MISC_SATEN register field. */
#define ALT_CLKMGR_PERPLL_MISC_SATEN_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_MISC_SATEN field value from a register. */
#define ALT_CLKMGR_PERPLL_MISC_SATEN_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_CLKMGR_PERPLL_MISC_SATEN register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_MISC_SATEN_SET(value) (((value) << 14) & 0x00004000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_PERPLL_MISC.
 */
struct ALT_CLKMGR_PERPLL_MISC_s
{
    uint32_t  bwadjen :  1;  /* Loop Bandwidth Adjust Enabled */
    uint32_t  bwadj   : 12;  /* Loop Bandwidth Adjust */
    uint32_t  fasten  :  1;  /* Fast Locking Enable */
    uint32_t  saten   :  1;  /* Saturation Enable */
    uint32_t          : 17;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_PERPLL_MISC. */
typedef volatile struct ALT_CLKMGR_PERPLL_MISC_s  ALT_CLKMGR_PERPLL_MISC_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_PERPLL_MISC register from the beginning of the component. */
#define ALT_CLKMGR_PERPLL_MISC_OFST        0x4

/*
 * Register : Peripheral PLL C0 Control Register for Clock emac0_clk - emac0clk
 * 
 * Contains settings that control clock emac0_clk generated from the C0 output of
 * the Peripheral PLL.
 * 
 * Only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [8:0]  | RW     | 0x1   | Counter    
 *  [31:9] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_EMAC0CLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_EMAC0CLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_EMAC0CLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_EMAC0CLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_PERPLL_EMAC0CLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_EMAC0CLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_PERPLL_EMAC0CLK_CNT register field value. */
#define ALT_CLKMGR_PERPLL_EMAC0CLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_PERPLL_EMAC0CLK_CNT register field value. */
#define ALT_CLKMGR_PERPLL_EMAC0CLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_PERPLL_EMAC0CLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_EMAC0CLK_CNT_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_EMAC0CLK_CNT field value from a register. */
#define ALT_CLKMGR_PERPLL_EMAC0CLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_PERPLL_EMAC0CLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_EMAC0CLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_PERPLL_EMAC0CLK.
 */
struct ALT_CLKMGR_PERPLL_EMAC0CLK_s
{
    uint32_t  cnt :  9;  /* Counter */
    uint32_t      : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_PERPLL_EMAC0CLK. */
typedef volatile struct ALT_CLKMGR_PERPLL_EMAC0CLK_s  ALT_CLKMGR_PERPLL_EMAC0CLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_PERPLL_EMAC0CLK register from the beginning of the component. */
#define ALT_CLKMGR_PERPLL_EMAC0CLK_OFST        0x8

/*
 * Register : Peripheral PLL C1 Control Register for Clock emac1_clk - emac1clk
 * 
 * Contains settings that control clock emac1_clk generated from the C1 output of
 * the Peripheral PLL.
 * 
 * Only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [8:0]  | RW     | 0x1   | Counter    
 *  [31:9] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_EMAC1CLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_EMAC1CLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_EMAC1CLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_EMAC1CLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_PERPLL_EMAC1CLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_EMAC1CLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_PERPLL_EMAC1CLK_CNT register field value. */
#define ALT_CLKMGR_PERPLL_EMAC1CLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_PERPLL_EMAC1CLK_CNT register field value. */
#define ALT_CLKMGR_PERPLL_EMAC1CLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_PERPLL_EMAC1CLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_EMAC1CLK_CNT_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_EMAC1CLK_CNT field value from a register. */
#define ALT_CLKMGR_PERPLL_EMAC1CLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_PERPLL_EMAC1CLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_EMAC1CLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_PERPLL_EMAC1CLK.
 */
struct ALT_CLKMGR_PERPLL_EMAC1CLK_s
{
    uint32_t  cnt :  9;  /* Counter */
    uint32_t      : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_PERPLL_EMAC1CLK. */
typedef volatile struct ALT_CLKMGR_PERPLL_EMAC1CLK_s  ALT_CLKMGR_PERPLL_EMAC1CLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_PERPLL_EMAC1CLK register from the beginning of the component. */
#define ALT_CLKMGR_PERPLL_EMAC1CLK_OFST        0xc

/*
 * Register : Peripheral PLL C2 Control Register for Clock periph_qspi_clk - perqspiclk
 * 
 * Contains settings that control clock periph_qspi_clk generated from the C2
 * output of the Peripheral PLL.
 * 
 * Only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [8:0]  | RW     | 0x1   | Counter    
 *  [31:9] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_PERQSPICLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_PERQSPICLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_PERQSPICLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_PERQSPICLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_PERPLL_PERQSPICLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_PERQSPICLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_PERPLL_PERQSPICLK_CNT register field value. */
#define ALT_CLKMGR_PERPLL_PERQSPICLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_PERPLL_PERQSPICLK_CNT register field value. */
#define ALT_CLKMGR_PERPLL_PERQSPICLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_PERPLL_PERQSPICLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_PERQSPICLK_CNT_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_PERQSPICLK_CNT field value from a register. */
#define ALT_CLKMGR_PERPLL_PERQSPICLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_PERPLL_PERQSPICLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_PERQSPICLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_PERPLL_PERQSPICLK.
 */
struct ALT_CLKMGR_PERPLL_PERQSPICLK_s
{
    uint32_t  cnt :  9;  /* Counter */
    uint32_t      : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_PERPLL_PERQSPICLK. */
typedef volatile struct ALT_CLKMGR_PERPLL_PERQSPICLK_s  ALT_CLKMGR_PERPLL_PERQSPICLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_PERPLL_PERQSPICLK register from the beginning of the component. */
#define ALT_CLKMGR_PERPLL_PERQSPICLK_OFST        0x10

/*
 * Register : Peripheral PLL C3 Control Register for Clock periph_nand_sdmmc_clk - pernandsdmmcclk
 * 
 * Contains settings that control clock periph_nand_sdmmc_clk generated from the C3
 * output of the Peripheral PLL.
 * 
 * Only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [8:0]  | RW     | 0x1   | Counter    
 *  [31:9] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT register field value. */
#define ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT register field value. */
#define ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT field value from a register. */
#define ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK.
 */
struct ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_s
{
    uint32_t  cnt :  9;  /* Counter */
    uint32_t      : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK. */
typedef volatile struct ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_s  ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK register from the beginning of the component. */
#define ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_OFST        0x14

/*
 * Register : Peripheral PLL C4 Control Register for Clock periph_base_clk - perbaseclk
 * 
 * Contains settings that control clock periph_base_clk generated from the C4
 * output of the Peripheral PLL.
 * 
 * Only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [8:0]  | RW     | 0x1   | Counter    
 *  [31:9] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_PERBASECLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_PERBASECLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_PERBASECLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_PERBASECLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_PERPLL_PERBASECLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_PERBASECLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_PERPLL_PERBASECLK_CNT register field value. */
#define ALT_CLKMGR_PERPLL_PERBASECLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_PERPLL_PERBASECLK_CNT register field value. */
#define ALT_CLKMGR_PERPLL_PERBASECLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_PERPLL_PERBASECLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_PERBASECLK_CNT_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_PERBASECLK_CNT field value from a register. */
#define ALT_CLKMGR_PERPLL_PERBASECLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_PERPLL_PERBASECLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_PERBASECLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_PERPLL_PERBASECLK.
 */
struct ALT_CLKMGR_PERPLL_PERBASECLK_s
{
    uint32_t  cnt :  9;  /* Counter */
    uint32_t      : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_PERPLL_PERBASECLK. */
typedef volatile struct ALT_CLKMGR_PERPLL_PERBASECLK_s  ALT_CLKMGR_PERPLL_PERBASECLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_PERPLL_PERBASECLK register from the beginning of the component. */
#define ALT_CLKMGR_PERPLL_PERBASECLK_OFST        0x18

/*
 * Register : Peripheral PLL C5 Control Register for Clock s2f_user1_clk - s2fuser1clk
 * 
 * Contains settings that control clock s2f_user1_clk generated from the C5 output
 * of the Peripheral PLL.
 * 
 * Qsys and user documenation refer to s2f_user1_clk as h2f_user1_clk.
 * 
 * Only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [8:0]  | RW     | 0x1   | Counter    
 *  [31:9] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT register field value. */
#define ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT register field value. */
#define ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT register field. */
#define ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT field value from a register. */
#define ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_S2FUSER1CLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_PERPLL_S2FUSER1CLK.
 */
struct ALT_CLKMGR_PERPLL_S2FUSER1CLK_s
{
    uint32_t  cnt :  9;  /* Counter */
    uint32_t      : 23;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_PERPLL_S2FUSER1CLK. */
typedef volatile struct ALT_CLKMGR_PERPLL_S2FUSER1CLK_s  ALT_CLKMGR_PERPLL_S2FUSER1CLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_PERPLL_S2FUSER1CLK register from the beginning of the component. */
#define ALT_CLKMGR_PERPLL_S2FUSER1CLK_OFST        0x1c

/*
 * Register : Enable Register - en
 * 
 * Contains fields that control clock enables for clocks derived from the
 * Peripheral PLL
 * 
 * 1: The clock is enabled.
 * 
 * 0: The clock is disabled.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description         
 * :--------|:-------|:------|:---------------------
 *  [0]     | RW     | 0x1   | emac0_clk Enable    
 *  [1]     | RW     | 0x1   | emac1_clk Enable    
 *  [2]     | RW     | 0x1   | usb_mp_clk Enable   
 *  [3]     | RW     | 0x1   | spi_m_clk Enable    
 *  [4]     | RW     | 0x1   | can0_clk Enable     
 *  [5]     | RW     | 0x1   | can1_clk Enable     
 *  [6]     | RW     | 0x1   | gpio_clk Enable     
 *  [7]     | RW     | 0x1   | s2f_user1_clk Enable
 *  [8]     | RW     | 0x1   | sdmmc_clk Enable    
 *  [9]     | RW     | 0x1   | nand_x_clk Enable   
 *  [10]    | RW     | 0x1   | nand_clk Enable     
 *  [11]    | RW     | 0x1   | qspi_clk Enable     
 *  [31:12] | ???    | 0x0   | *UNDEFINED*         
 * 
 */
/*
 * Field : emac0_clk Enable - emac0clk
 * 
 * Enables clock emac0_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_EN_EMAC0CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_EMAC0CLK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_EN_EMAC0CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_EMAC0CLK_MSB        0
/* The width in bits of the ALT_CLKMGR_PERPLL_EN_EMAC0CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_EMAC0CLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_EN_EMAC0CLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_EMAC0CLK_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_PERPLL_EN_EMAC0CLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_EMAC0CLK_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_PERPLL_EN_EMAC0CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_EMAC0CLK_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_EN_EMAC0CLK field value from a register. */
#define ALT_CLKMGR_PERPLL_EN_EMAC0CLK_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_PERPLL_EN_EMAC0CLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_EN_EMAC0CLK_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : emac1_clk Enable - emac1clk
 * 
 * Enables clock emac1_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_EN_EMAC1CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_EMAC1CLK_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_EN_EMAC1CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_EMAC1CLK_MSB        1
/* The width in bits of the ALT_CLKMGR_PERPLL_EN_EMAC1CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_EMAC1CLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_EN_EMAC1CLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_EMAC1CLK_SET_MSK    0x00000002
/* The mask used to clear the ALT_CLKMGR_PERPLL_EN_EMAC1CLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_EMAC1CLK_CLR_MSK    0xfffffffd
/* The reset value of the ALT_CLKMGR_PERPLL_EN_EMAC1CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_EMAC1CLK_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_EN_EMAC1CLK field value from a register. */
#define ALT_CLKMGR_PERPLL_EN_EMAC1CLK_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_CLKMGR_PERPLL_EN_EMAC1CLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_EN_EMAC1CLK_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : usb_mp_clk Enable - usbclk
 * 
 * Enables clock usb_mp_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_EN_USBCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_USBCLK_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_EN_USBCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_USBCLK_MSB        2
/* The width in bits of the ALT_CLKMGR_PERPLL_EN_USBCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_USBCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_EN_USBCLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_USBCLK_SET_MSK    0x00000004
/* The mask used to clear the ALT_CLKMGR_PERPLL_EN_USBCLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_USBCLK_CLR_MSK    0xfffffffb
/* The reset value of the ALT_CLKMGR_PERPLL_EN_USBCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_USBCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_EN_USBCLK field value from a register. */
#define ALT_CLKMGR_PERPLL_EN_USBCLK_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_CLKMGR_PERPLL_EN_USBCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_EN_USBCLK_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : spi_m_clk Enable - spimclk
 * 
 * Enables clock spi_m_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_EN_SPIMCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_SPIMCLK_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_EN_SPIMCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_SPIMCLK_MSB        3
/* The width in bits of the ALT_CLKMGR_PERPLL_EN_SPIMCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_SPIMCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_EN_SPIMCLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_SPIMCLK_SET_MSK    0x00000008
/* The mask used to clear the ALT_CLKMGR_PERPLL_EN_SPIMCLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_SPIMCLK_CLR_MSK    0xfffffff7
/* The reset value of the ALT_CLKMGR_PERPLL_EN_SPIMCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_SPIMCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_EN_SPIMCLK field value from a register. */
#define ALT_CLKMGR_PERPLL_EN_SPIMCLK_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_CLKMGR_PERPLL_EN_SPIMCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_EN_SPIMCLK_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : can0_clk Enable - can0clk
 * 
 * Enables clock can0_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_EN_CAN0CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_CAN0CLK_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_EN_CAN0CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_CAN0CLK_MSB        4
/* The width in bits of the ALT_CLKMGR_PERPLL_EN_CAN0CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_CAN0CLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_EN_CAN0CLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_CAN0CLK_SET_MSK    0x00000010
/* The mask used to clear the ALT_CLKMGR_PERPLL_EN_CAN0CLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_CAN0CLK_CLR_MSK    0xffffffef
/* The reset value of the ALT_CLKMGR_PERPLL_EN_CAN0CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_CAN0CLK_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_EN_CAN0CLK field value from a register. */
#define ALT_CLKMGR_PERPLL_EN_CAN0CLK_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_CLKMGR_PERPLL_EN_CAN0CLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_EN_CAN0CLK_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : can1_clk Enable - can1clk
 * 
 * Enables clock can1_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_EN_CAN1CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_CAN1CLK_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_EN_CAN1CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_CAN1CLK_MSB        5
/* The width in bits of the ALT_CLKMGR_PERPLL_EN_CAN1CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_CAN1CLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_EN_CAN1CLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_CAN1CLK_SET_MSK    0x00000020
/* The mask used to clear the ALT_CLKMGR_PERPLL_EN_CAN1CLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_CAN1CLK_CLR_MSK    0xffffffdf
/* The reset value of the ALT_CLKMGR_PERPLL_EN_CAN1CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_CAN1CLK_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_EN_CAN1CLK field value from a register. */
#define ALT_CLKMGR_PERPLL_EN_CAN1CLK_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_CLKMGR_PERPLL_EN_CAN1CLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_EN_CAN1CLK_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : gpio_clk Enable - gpioclk
 * 
 * Enables clock gpio_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_EN_GPIOCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_GPIOCLK_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_EN_GPIOCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_GPIOCLK_MSB        6
/* The width in bits of the ALT_CLKMGR_PERPLL_EN_GPIOCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_GPIOCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_EN_GPIOCLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_GPIOCLK_SET_MSK    0x00000040
/* The mask used to clear the ALT_CLKMGR_PERPLL_EN_GPIOCLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_GPIOCLK_CLR_MSK    0xffffffbf
/* The reset value of the ALT_CLKMGR_PERPLL_EN_GPIOCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_GPIOCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_EN_GPIOCLK field value from a register. */
#define ALT_CLKMGR_PERPLL_EN_GPIOCLK_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_CLKMGR_PERPLL_EN_GPIOCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_EN_GPIOCLK_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : s2f_user1_clk Enable - s2fuser1clk
 * 
 * Enables clock s2f_user1_clk output.
 * 
 * Qsys and user documenation refer to s2f_user1_clk as h2f_user1_clk.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK_MSB        7
/* The width in bits of the ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK_SET_MSK    0x00000080
/* The mask used to clear the ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK_CLR_MSK    0xffffff7f
/* The reset value of the ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK register field. */
#define ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK field value from a register. */
#define ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_EN_S2FUSER1CLK_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : sdmmc_clk Enable - sdmmcclk
 * 
 * Enables clock sdmmc_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_EN_SDMMCCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_SDMMCCLK_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_EN_SDMMCCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_SDMMCCLK_MSB        8
/* The width in bits of the ALT_CLKMGR_PERPLL_EN_SDMMCCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_SDMMCCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_EN_SDMMCCLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_SDMMCCLK_SET_MSK    0x00000100
/* The mask used to clear the ALT_CLKMGR_PERPLL_EN_SDMMCCLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_SDMMCCLK_CLR_MSK    0xfffffeff
/* The reset value of the ALT_CLKMGR_PERPLL_EN_SDMMCCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_SDMMCCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_EN_SDMMCCLK field value from a register. */
#define ALT_CLKMGR_PERPLL_EN_SDMMCCLK_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_CLKMGR_PERPLL_EN_SDMMCCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_EN_SDMMCCLK_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : nand_x_clk Enable - nandxclk
 * 
 * Enables clock nand_x_clk output
 * 
 * nand_clk Enable should always be de-asserted before the nand_x_clk Enable, and
 * the nand_x_clk Enable should always be asserted before the nand_clk Enable is
 * asserted. A brief delay is also required between switching the enables (8 *
 * nand_clk period).
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_EN_NANDXCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_NANDXCLK_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_EN_NANDXCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_NANDXCLK_MSB        9
/* The width in bits of the ALT_CLKMGR_PERPLL_EN_NANDXCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_NANDXCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_EN_NANDXCLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_NANDXCLK_SET_MSK    0x00000200
/* The mask used to clear the ALT_CLKMGR_PERPLL_EN_NANDXCLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_NANDXCLK_CLR_MSK    0xfffffdff
/* The reset value of the ALT_CLKMGR_PERPLL_EN_NANDXCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_NANDXCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_EN_NANDXCLK field value from a register. */
#define ALT_CLKMGR_PERPLL_EN_NANDXCLK_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_CLKMGR_PERPLL_EN_NANDXCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_EN_NANDXCLK_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : nand_clk Enable - nandclk
 * 
 * Enables clock nand_clk output
 * 
 * nand_clk Enable should always be de-asserted before the nand_x_clk Enable, and
 * the nand_x_clk Enable should always be asserted before the nand_clk Enable is
 * asserted. A brief delay is also required between switching the enables (8 *
 * nand_clk period).
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_EN_NANDCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_NANDCLK_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_EN_NANDCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_NANDCLK_MSB        10
/* The width in bits of the ALT_CLKMGR_PERPLL_EN_NANDCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_NANDCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_EN_NANDCLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_NANDCLK_SET_MSK    0x00000400
/* The mask used to clear the ALT_CLKMGR_PERPLL_EN_NANDCLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_NANDCLK_CLR_MSK    0xfffffbff
/* The reset value of the ALT_CLKMGR_PERPLL_EN_NANDCLK register field. */
#define ALT_CLKMGR_PERPLL_EN_NANDCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_EN_NANDCLK field value from a register. */
#define ALT_CLKMGR_PERPLL_EN_NANDCLK_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_CLKMGR_PERPLL_EN_NANDCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_EN_NANDCLK_SET(value) (((value) << 10) & 0x00000400)

/*
 * Field : qspi_clk Enable - qspiclk
 * 
 * Enables clock qspi_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_EN_QSPICLK register field. */
#define ALT_CLKMGR_PERPLL_EN_QSPICLK_LSB        11
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_EN_QSPICLK register field. */
#define ALT_CLKMGR_PERPLL_EN_QSPICLK_MSB        11
/* The width in bits of the ALT_CLKMGR_PERPLL_EN_QSPICLK register field. */
#define ALT_CLKMGR_PERPLL_EN_QSPICLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_PERPLL_EN_QSPICLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_QSPICLK_SET_MSK    0x00000800
/* The mask used to clear the ALT_CLKMGR_PERPLL_EN_QSPICLK register field value. */
#define ALT_CLKMGR_PERPLL_EN_QSPICLK_CLR_MSK    0xfffff7ff
/* The reset value of the ALT_CLKMGR_PERPLL_EN_QSPICLK register field. */
#define ALT_CLKMGR_PERPLL_EN_QSPICLK_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_EN_QSPICLK field value from a register. */
#define ALT_CLKMGR_PERPLL_EN_QSPICLK_GET(value) (((value) & 0x00000800) >> 11)
/* Produces a ALT_CLKMGR_PERPLL_EN_QSPICLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_EN_QSPICLK_SET(value) (((value) << 11) & 0x00000800)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_PERPLL_EN.
 */
struct ALT_CLKMGR_PERPLL_EN_s
{
    uint32_t  emac0clk    :  1;  /* emac0_clk Enable */
    uint32_t  emac1clk    :  1;  /* emac1_clk Enable */
    uint32_t  usbclk      :  1;  /* usb_mp_clk Enable */
    uint32_t  spimclk     :  1;  /* spi_m_clk Enable */
    uint32_t  can0clk     :  1;  /* can0_clk Enable */
    uint32_t  can1clk     :  1;  /* can1_clk Enable */
    uint32_t  gpioclk     :  1;  /* gpio_clk Enable */
    uint32_t  s2fuser1clk :  1;  /* s2f_user1_clk Enable */
    uint32_t  sdmmcclk    :  1;  /* sdmmc_clk Enable */
    uint32_t  nandxclk    :  1;  /* nand_x_clk Enable */
    uint32_t  nandclk     :  1;  /* nand_clk Enable */
    uint32_t  qspiclk     :  1;  /* qspi_clk Enable */
    uint32_t              : 20;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_PERPLL_EN. */
typedef volatile struct ALT_CLKMGR_PERPLL_EN_s  ALT_CLKMGR_PERPLL_EN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_PERPLL_EN register from the beginning of the component. */
#define ALT_CLKMGR_PERPLL_EN_OFST        0x20

/*
 * Register : Divide Register - div
 * 
 * Contains fields that control clock dividers for clocks derived from the
 * Peripheral PLL
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description             
 * :--------|:-------|:------|:-------------------------
 *  [2:0]   | RW     | 0x0   | USB Clock Divider       
 *  [5:3]   | RW     | 0x0   | SPI Master Clock Divider
 *  [8:6]   | RW     | 0x0   | CAN0 Clock Divider      
 *  [11:9]  | RW     | 0x0   | CAN1 Clock Divider      
 *  [31:12] | ???    | 0x0   | *UNDEFINED*             
 * 
 */
/*
 * Field : USB Clock Divider - usbclk
 * 
 * The usb_mp_clk is divided down from the periph_base_clk by the value specified
 * in this field.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description 
 * :--------------------------------------|:------|:-------------
 *  ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV1   | 0x0   | Divide By 1 
 *  ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV2   | 0x1   | Divide By 2 
 *  ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV4   | 0x2   | Divide By 4 
 *  ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV8   | 0x3   | Divide By 8 
 *  ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV16  | 0x4   | Divide By 16
 *  ALT_CLKMGR_PERPLL_DIV_USBCLK_E_RSVD_1 | 0x5   | Reserved    
 *  ALT_CLKMGR_PERPLL_DIV_USBCLK_E_RSVD_2 | 0x6   | Reserved    
 *  ALT_CLKMGR_PERPLL_DIV_USBCLK_E_RSVD_3 | 0x7   | Reserved    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_USBCLK
 * 
 * Divide By 1
 */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV1     0x0
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_USBCLK
 * 
 * Divide By 2
 */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV2     0x1
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_USBCLK
 * 
 * Divide By 4
 */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV4     0x2
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_USBCLK
 * 
 * Divide By 8
 */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV8     0x3
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_USBCLK
 * 
 * Divide By 16
 */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_E_DIV16    0x4
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_USBCLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_E_RSVD_1   0x5
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_USBCLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_E_RSVD_2   0x6
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_USBCLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_E_RSVD_3   0x7

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_DIV_USBCLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_DIV_USBCLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_MSB        2
/* The width in bits of the ALT_CLKMGR_PERPLL_DIV_USBCLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_WIDTH      3
/* The mask used to set the ALT_CLKMGR_PERPLL_DIV_USBCLK register field value. */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_SET_MSK    0x00000007
/* The mask used to clear the ALT_CLKMGR_PERPLL_DIV_USBCLK register field value. */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_CLR_MSK    0xfffffff8
/* The reset value of the ALT_CLKMGR_PERPLL_DIV_USBCLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_RESET      0x0
/* Extracts the ALT_CLKMGR_PERPLL_DIV_USBCLK field value from a register. */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_GET(value) (((value) & 0x00000007) >> 0)
/* Produces a ALT_CLKMGR_PERPLL_DIV_USBCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_DIV_USBCLK_SET(value) (((value) << 0) & 0x00000007)

/*
 * Field : SPI Master Clock Divider - spimclk
 * 
 * The spi_m_clk is divided down from the periph_base_clk by the value specified in
 * this field.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description 
 * :---------------------------------------|:------|:-------------
 *  ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV1   | 0x0   | Divide By 1 
 *  ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV2   | 0x1   | Divide By 2 
 *  ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV4   | 0x2   | Divide By 4 
 *  ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV8   | 0x3   | Divide By 8 
 *  ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV16  | 0x4   | Divide By 16
 *  ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_RSVD_1 | 0x5   | Reserved    
 *  ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_RSVD_2 | 0x6   | Reserved    
 *  ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_RSVD_3 | 0x7   | Reserved    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_SPIMCLK
 * 
 * Divide By 1
 */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV1    0x0
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_SPIMCLK
 * 
 * Divide By 2
 */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV2    0x1
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_SPIMCLK
 * 
 * Divide By 4
 */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV4    0x2
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_SPIMCLK
 * 
 * Divide By 8
 */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV8    0x3
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_SPIMCLK
 * 
 * Divide By 16
 */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_DIV16   0x4
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_SPIMCLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_RSVD_1  0x5
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_SPIMCLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_RSVD_2  0x6
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_SPIMCLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_E_RSVD_3  0x7

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_DIV_SPIMCLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_DIV_SPIMCLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_MSB        5
/* The width in bits of the ALT_CLKMGR_PERPLL_DIV_SPIMCLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_WIDTH      3
/* The mask used to set the ALT_CLKMGR_PERPLL_DIV_SPIMCLK register field value. */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_SET_MSK    0x00000038
/* The mask used to clear the ALT_CLKMGR_PERPLL_DIV_SPIMCLK register field value. */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_CLR_MSK    0xffffffc7
/* The reset value of the ALT_CLKMGR_PERPLL_DIV_SPIMCLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_RESET      0x0
/* Extracts the ALT_CLKMGR_PERPLL_DIV_SPIMCLK field value from a register. */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_GET(value) (((value) & 0x00000038) >> 3)
/* Produces a ALT_CLKMGR_PERPLL_DIV_SPIMCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_DIV_SPIMCLK_SET(value) (((value) << 3) & 0x00000038)

/*
 * Field : CAN0 Clock Divider - can0clk
 * 
 * The can0_clk is divided down from the periph_base_clk by the value specified in
 * this field.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description 
 * :---------------------------------------|:------|:-------------
 *  ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV1   | 0x0   | Divide By 1 
 *  ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV2   | 0x1   | Divide By 2 
 *  ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV4   | 0x2   | Divide By 4 
 *  ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV8   | 0x3   | Divide By 8 
 *  ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV16  | 0x4   | Divide By 16
 *  ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_RSVD_1 | 0x5   | Reserved    
 *  ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_RSVD_2 | 0x6   | Reserved    
 *  ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_RSVD_3 | 0x7   | Reserved    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN0CLK
 * 
 * Divide By 1
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV1    0x0
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN0CLK
 * 
 * Divide By 2
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV2    0x1
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN0CLK
 * 
 * Divide By 4
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV4    0x2
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN0CLK
 * 
 * Divide By 8
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV8    0x3
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN0CLK
 * 
 * Divide By 16
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_DIV16   0x4
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN0CLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_RSVD_1  0x5
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN0CLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_RSVD_2  0x6
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN0CLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_E_RSVD_3  0x7

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_DIV_CAN0CLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_DIV_CAN0CLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_MSB        8
/* The width in bits of the ALT_CLKMGR_PERPLL_DIV_CAN0CLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_WIDTH      3
/* The mask used to set the ALT_CLKMGR_PERPLL_DIV_CAN0CLK register field value. */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_SET_MSK    0x000001c0
/* The mask used to clear the ALT_CLKMGR_PERPLL_DIV_CAN0CLK register field value. */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_CLR_MSK    0xfffffe3f
/* The reset value of the ALT_CLKMGR_PERPLL_DIV_CAN0CLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_RESET      0x0
/* Extracts the ALT_CLKMGR_PERPLL_DIV_CAN0CLK field value from a register. */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_GET(value) (((value) & 0x000001c0) >> 6)
/* Produces a ALT_CLKMGR_PERPLL_DIV_CAN0CLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_DIV_CAN0CLK_SET(value) (((value) << 6) & 0x000001c0)

/*
 * Field : CAN1 Clock Divider - can1clk
 * 
 * The can1_clk is divided down from the periph_base_clk by the value specified in
 * this field.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description 
 * :---------------------------------------|:------|:-------------
 *  ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV1   | 0x0   | Divide By 1 
 *  ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV2   | 0x1   | Divide By 2 
 *  ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV4   | 0x2   | Divide By 4 
 *  ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV8   | 0x3   | Divide By 8 
 *  ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV16  | 0x4   | Divide By 16
 *  ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_RSVD_1 | 0x5   | Reserved    
 *  ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_RSVD_2 | 0x6   | Reserved    
 *  ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_RSVD_3 | 0x7   | Reserved    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN1CLK
 * 
 * Divide By 1
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV1    0x0
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN1CLK
 * 
 * Divide By 2
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV2    0x1
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN1CLK
 * 
 * Divide By 4
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV4    0x2
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN1CLK
 * 
 * Divide By 8
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV8    0x3
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN1CLK
 * 
 * Divide By 16
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_DIV16   0x4
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN1CLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_RSVD_1  0x5
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN1CLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_RSVD_2  0x6
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_DIV_CAN1CLK
 * 
 * Reserved
 */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_E_RSVD_3  0x7

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_DIV_CAN1CLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_DIV_CAN1CLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_MSB        11
/* The width in bits of the ALT_CLKMGR_PERPLL_DIV_CAN1CLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_WIDTH      3
/* The mask used to set the ALT_CLKMGR_PERPLL_DIV_CAN1CLK register field value. */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_SET_MSK    0x00000e00
/* The mask used to clear the ALT_CLKMGR_PERPLL_DIV_CAN1CLK register field value. */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_CLR_MSK    0xfffff1ff
/* The reset value of the ALT_CLKMGR_PERPLL_DIV_CAN1CLK register field. */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_RESET      0x0
/* Extracts the ALT_CLKMGR_PERPLL_DIV_CAN1CLK field value from a register. */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_GET(value) (((value) & 0x00000e00) >> 9)
/* Produces a ALT_CLKMGR_PERPLL_DIV_CAN1CLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_DIV_CAN1CLK_SET(value) (((value) << 9) & 0x00000e00)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_PERPLL_DIV.
 */
struct ALT_CLKMGR_PERPLL_DIV_s
{
    uint32_t  usbclk  :  3;  /* USB Clock Divider */
    uint32_t  spimclk :  3;  /* SPI Master Clock Divider */
    uint32_t  can0clk :  3;  /* CAN0 Clock Divider */
    uint32_t  can1clk :  3;  /* CAN1 Clock Divider */
    uint32_t          : 20;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_PERPLL_DIV. */
typedef volatile struct ALT_CLKMGR_PERPLL_DIV_s  ALT_CLKMGR_PERPLL_DIV_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_PERPLL_DIV register from the beginning of the component. */
#define ALT_CLKMGR_PERPLL_DIV_OFST        0x24

/*
 * Register : GPIO Divide Register - gpiodiv
 * 
 * Contains a field that controls the clock divider for the GPIO De-bounce clock.
 * 
 * Only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                 
 * :--------|:-------|:------|:-----------------------------
 *  [23:0]  | RW     | 0x1   | GPIO De-bounce Clock Divider
 *  [31:24] | ???    | 0x0   | *UNDEFINED*                 
 * 
 */
/*
 * Field : GPIO De-bounce Clock Divider - gpiodbclk
 * 
 * The gpio_db_clk is divided down from the periph_base_clk by the value plus one
 * specified in this field. The value 0 (divide by 1) is illegal. A value of 1
 * indicates divide by 2, 2 divide by 3, etc.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK register field. */
#define ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK register field. */
#define ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK_MSB        23
/* The width in bits of the ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK register field. */
#define ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK_WIDTH      24
/* The mask used to set the ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK register field value. */
#define ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK_SET_MSK    0x00ffffff
/* The mask used to clear the ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK register field value. */
#define ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK_CLR_MSK    0xff000000
/* The reset value of the ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK register field. */
#define ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK field value from a register. */
#define ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK_GET(value) (((value) & 0x00ffffff) >> 0)
/* Produces a ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_GPIODIV_GPIODBCLK_SET(value) (((value) << 0) & 0x00ffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_PERPLL_GPIODIV.
 */
struct ALT_CLKMGR_PERPLL_GPIODIV_s
{
    uint32_t  gpiodbclk : 24;  /* GPIO De-bounce Clock Divider */
    uint32_t            :  8;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_PERPLL_GPIODIV. */
typedef volatile struct ALT_CLKMGR_PERPLL_GPIODIV_s  ALT_CLKMGR_PERPLL_GPIODIV_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_PERPLL_GPIODIV register from the beginning of the component. */
#define ALT_CLKMGR_PERPLL_GPIODIV_OFST        0x28

/*
 * Register : Flash Clock Source Register - src
 * 
 * Contains fields that select the source clocks for the flash controllers.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description       
 * :-------|:-------|:------|:-------------------
 *  [1:0]  | RW     | 0x1   | SDMMC Clock Source
 *  [3:2]  | RW     | 0x1   | NAND Clock Source 
 *  [5:4]  | RW     | 0x1   | QSPI Clock Source 
 *  [31:6] | ???    | 0x0   | *UNDEFINED*       
 * 
 */
/*
 * Field : SDMMC Clock Source - sdmmc
 * 
 * Selects the source clock for the SDMMC.
 * 
 * Qsys and user documenation refer to f2s_periph_ref_clk as f2h_periph_ref_clk.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                             | Value | Description          
 * :-------------------------------------------------|:------|:----------------------
 *  ALT_CLKMGR_PERPLL_SRC_SDMMC_E_F2S_PERIPH_REF_CLK | 0x0   | f2s_periph_ref_clk   
 *  ALT_CLKMGR_PERPLL_SRC_SDMMC_E_MAIN_NAND_CLK      | 0x1   | main_nand_sdmmc_clk  
 *  ALT_CLKMGR_PERPLL_SRC_SDMMC_E_PERIPH_NAND_CLK    | 0x2   | periph_nand_sdmmc_clk
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_SRC_SDMMC
 * 
 * f2s_periph_ref_clk
 */
#define ALT_CLKMGR_PERPLL_SRC_SDMMC_E_F2S_PERIPH_REF_CLK    0x0
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_SRC_SDMMC
 * 
 * main_nand_sdmmc_clk
 */
#define ALT_CLKMGR_PERPLL_SRC_SDMMC_E_MAIN_NAND_CLK         0x1
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_SRC_SDMMC
 * 
 * periph_nand_sdmmc_clk
 */
#define ALT_CLKMGR_PERPLL_SRC_SDMMC_E_PERIPH_NAND_CLK       0x2

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_SRC_SDMMC register field. */
#define ALT_CLKMGR_PERPLL_SRC_SDMMC_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_SRC_SDMMC register field. */
#define ALT_CLKMGR_PERPLL_SRC_SDMMC_MSB        1
/* The width in bits of the ALT_CLKMGR_PERPLL_SRC_SDMMC register field. */
#define ALT_CLKMGR_PERPLL_SRC_SDMMC_WIDTH      2
/* The mask used to set the ALT_CLKMGR_PERPLL_SRC_SDMMC register field value. */
#define ALT_CLKMGR_PERPLL_SRC_SDMMC_SET_MSK    0x00000003
/* The mask used to clear the ALT_CLKMGR_PERPLL_SRC_SDMMC register field value. */
#define ALT_CLKMGR_PERPLL_SRC_SDMMC_CLR_MSK    0xfffffffc
/* The reset value of the ALT_CLKMGR_PERPLL_SRC_SDMMC register field. */
#define ALT_CLKMGR_PERPLL_SRC_SDMMC_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_SRC_SDMMC field value from a register. */
#define ALT_CLKMGR_PERPLL_SRC_SDMMC_GET(value) (((value) & 0x00000003) >> 0)
/* Produces a ALT_CLKMGR_PERPLL_SRC_SDMMC register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_SRC_SDMMC_SET(value) (((value) << 0) & 0x00000003)

/*
 * Field : NAND Clock Source - nand
 * 
 * Selects the source clock for the NAND.
 * 
 * Qsys and user documenation refer to f2s_periph_ref_clk as f2h_periph_ref_clk.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                            | Value | Description          
 * :------------------------------------------------|:------|:----------------------
 *  ALT_CLKMGR_PERPLL_SRC_NAND_E_F2S_PERIPH_REF_CLK | 0x0   | f2s_periph_ref_clk   
 *  ALT_CLKMGR_PERPLL_SRC_NAND_E_MAIN_NAND_CLK      | 0x1   | main_nand_sdmmc_clk  
 *  ALT_CLKMGR_PERPLL_SRC_NAND_E_PERIPH_NAND_CLK    | 0x2   | periph_nand_sdmmc_clk
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_SRC_NAND
 * 
 * f2s_periph_ref_clk
 */
#define ALT_CLKMGR_PERPLL_SRC_NAND_E_F2S_PERIPH_REF_CLK 0x0
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_SRC_NAND
 * 
 * main_nand_sdmmc_clk
 */
#define ALT_CLKMGR_PERPLL_SRC_NAND_E_MAIN_NAND_CLK      0x1
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_SRC_NAND
 * 
 * periph_nand_sdmmc_clk
 */
#define ALT_CLKMGR_PERPLL_SRC_NAND_E_PERIPH_NAND_CLK    0x2

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_SRC_NAND register field. */
#define ALT_CLKMGR_PERPLL_SRC_NAND_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_SRC_NAND register field. */
#define ALT_CLKMGR_PERPLL_SRC_NAND_MSB        3
/* The width in bits of the ALT_CLKMGR_PERPLL_SRC_NAND register field. */
#define ALT_CLKMGR_PERPLL_SRC_NAND_WIDTH      2
/* The mask used to set the ALT_CLKMGR_PERPLL_SRC_NAND register field value. */
#define ALT_CLKMGR_PERPLL_SRC_NAND_SET_MSK    0x0000000c
/* The mask used to clear the ALT_CLKMGR_PERPLL_SRC_NAND register field value. */
#define ALT_CLKMGR_PERPLL_SRC_NAND_CLR_MSK    0xfffffff3
/* The reset value of the ALT_CLKMGR_PERPLL_SRC_NAND register field. */
#define ALT_CLKMGR_PERPLL_SRC_NAND_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_SRC_NAND field value from a register. */
#define ALT_CLKMGR_PERPLL_SRC_NAND_GET(value) (((value) & 0x0000000c) >> 2)
/* Produces a ALT_CLKMGR_PERPLL_SRC_NAND register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_SRC_NAND_SET(value) (((value) << 2) & 0x0000000c)

/*
 * Field : QSPI Clock Source - qspi
 * 
 * Selects the source clock for the QSPI.
 * 
 * Qsys and user documenation refer to f2s_periph_ref_clk as f2h_periph_ref_clk.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                            | Value | Description       
 * :------------------------------------------------|:------|:-------------------
 *  ALT_CLKMGR_PERPLL_SRC_QSPI_E_F2S_PERIPH_REF_CLK | 0x0   | f2s_periph_ref_clk
 *  ALT_CLKMGR_PERPLL_SRC_QSPI_E_MAIN_QSPI_CLK      | 0x1   | main_qspi_clk     
 *  ALT_CLKMGR_PERPLL_SRC_QSPI_E_PERIPH_QSPI_CLK    | 0x2   | periph_qspi_clk   
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_SRC_QSPI
 * 
 * f2s_periph_ref_clk
 */
#define ALT_CLKMGR_PERPLL_SRC_QSPI_E_F2S_PERIPH_REF_CLK 0x0
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_SRC_QSPI
 * 
 * main_qspi_clk
 */
#define ALT_CLKMGR_PERPLL_SRC_QSPI_E_MAIN_QSPI_CLK      0x1
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_SRC_QSPI
 * 
 * periph_qspi_clk
 */
#define ALT_CLKMGR_PERPLL_SRC_QSPI_E_PERIPH_QSPI_CLK    0x2

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_SRC_QSPI register field. */
#define ALT_CLKMGR_PERPLL_SRC_QSPI_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_SRC_QSPI register field. */
#define ALT_CLKMGR_PERPLL_SRC_QSPI_MSB        5
/* The width in bits of the ALT_CLKMGR_PERPLL_SRC_QSPI register field. */
#define ALT_CLKMGR_PERPLL_SRC_QSPI_WIDTH      2
/* The mask used to set the ALT_CLKMGR_PERPLL_SRC_QSPI register field value. */
#define ALT_CLKMGR_PERPLL_SRC_QSPI_SET_MSK    0x00000030
/* The mask used to clear the ALT_CLKMGR_PERPLL_SRC_QSPI register field value. */
#define ALT_CLKMGR_PERPLL_SRC_QSPI_CLR_MSK    0xffffffcf
/* The reset value of the ALT_CLKMGR_PERPLL_SRC_QSPI register field. */
#define ALT_CLKMGR_PERPLL_SRC_QSPI_RESET      0x1
/* Extracts the ALT_CLKMGR_PERPLL_SRC_QSPI field value from a register. */
#define ALT_CLKMGR_PERPLL_SRC_QSPI_GET(value) (((value) & 0x00000030) >> 4)
/* Produces a ALT_CLKMGR_PERPLL_SRC_QSPI register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_SRC_QSPI_SET(value) (((value) << 4) & 0x00000030)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_PERPLL_SRC.
 */
struct ALT_CLKMGR_PERPLL_SRC_s
{
    uint32_t  sdmmc :  2;  /* SDMMC Clock Source */
    uint32_t  nand  :  2;  /* NAND Clock Source */
    uint32_t  qspi  :  2;  /* QSPI Clock Source */
    uint32_t        : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_PERPLL_SRC. */
typedef volatile struct ALT_CLKMGR_PERPLL_SRC_s  ALT_CLKMGR_PERPLL_SRC_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_PERPLL_SRC register from the beginning of the component. */
#define ALT_CLKMGR_PERPLL_SRC_OFST        0x2c

/*
 * Register : Peripheral PLL Output Counter Reset Ack Status Register - stat
 * 
 * Contains Output Clock Counter Reset acknowledge status.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                     
 * :-------|:-------|:------|:---------------------------------
 *  [5:0]  | R      | 0x0   | Output Counter Reset Acknowledge
 *  [31:6] | ???    | 0x0   | *UNDEFINED*                     
 * 
 */
/*
 * Field : Output Counter Reset Acknowledge - outresetack
 * 
 * These read only bits per PLL output indicate that the PLL has received the
 * Output Reset Counter request and has gracefully stopped the respective PLL
 * output clock.
 * 
 * For software to change the PLL output counter without producing glitches on the
 * respective clock, SW must set the VCO register respective Output Counter Reset
 * bit. Software then polls the respective Output Counter Reset Acknowledge bit in
 * the Output Counter Reset Ack Status Register. Software then writes the
 * appropriate counter register, and then clears the respective VCO register Output
 * Counter Reset bit.
 * 
 * The reset value of this bit is applied on a cold reset; warm reset has no affect
 * on this bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                       | Value | Description                         
 * :-------------------------------------------|:------|:-------------------------------------
 *  ALT_CLKMGR_PERPLL_STAT_OUTRSTACK_E_IDLE    | 0x0   | Idle                                
 *  ALT_CLKMGR_PERPLL_STAT_OUTRSTACK_E_ACK_RXD | 0x1   | Output Counter Acknowledge received.
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_STAT_OUTRSTACK
 * 
 * Idle
 */
#define ALT_CLKMGR_PERPLL_STAT_OUTRSTACK_E_IDLE     0x0
/*
 * Enumerated value for register field ALT_CLKMGR_PERPLL_STAT_OUTRSTACK
 * 
 * Output Counter Acknowledge received.
 */
#define ALT_CLKMGR_PERPLL_STAT_OUTRSTACK_E_ACK_RXD  0x1

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_PERPLL_STAT_OUTRSTACK register field. */
#define ALT_CLKMGR_PERPLL_STAT_OUTRSTACK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_PERPLL_STAT_OUTRSTACK register field. */
#define ALT_CLKMGR_PERPLL_STAT_OUTRSTACK_MSB        5
/* The width in bits of the ALT_CLKMGR_PERPLL_STAT_OUTRSTACK register field. */
#define ALT_CLKMGR_PERPLL_STAT_OUTRSTACK_WIDTH      6
/* The mask used to set the ALT_CLKMGR_PERPLL_STAT_OUTRSTACK register field value. */
#define ALT_CLKMGR_PERPLL_STAT_OUTRSTACK_SET_MSK    0x0000003f
/* The mask used to clear the ALT_CLKMGR_PERPLL_STAT_OUTRSTACK register field value. */
#define ALT_CLKMGR_PERPLL_STAT_OUTRSTACK_CLR_MSK    0xffffffc0
/* The reset value of the ALT_CLKMGR_PERPLL_STAT_OUTRSTACK register field. */
#define ALT_CLKMGR_PERPLL_STAT_OUTRSTACK_RESET      0x0
/* Extracts the ALT_CLKMGR_PERPLL_STAT_OUTRSTACK field value from a register. */
#define ALT_CLKMGR_PERPLL_STAT_OUTRSTACK_GET(value) (((value) & 0x0000003f) >> 0)
/* Produces a ALT_CLKMGR_PERPLL_STAT_OUTRSTACK register field value suitable for setting the register. */
#define ALT_CLKMGR_PERPLL_STAT_OUTRSTACK_SET(value) (((value) << 0) & 0x0000003f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_PERPLL_STAT.
 */
struct ALT_CLKMGR_PERPLL_STAT_s
{
    const uint32_t  outresetack :  6;  /* Output Counter Reset Acknowledge */
    uint32_t                    : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_PERPLL_STAT. */
typedef volatile struct ALT_CLKMGR_PERPLL_STAT_s  ALT_CLKMGR_PERPLL_STAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_PERPLL_STAT register from the beginning of the component. */
#define ALT_CLKMGR_PERPLL_STAT_OFST        0x30

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_CLKMGR_PERPLL.
 */
struct ALT_CLKMGR_PERPLL_s
{
    volatile ALT_CLKMGR_PERPLL_VCO_t              vco;                /* ALT_CLKMGR_PERPLL_VCO */
    volatile ALT_CLKMGR_PERPLL_MISC_t             misc;               /* ALT_CLKMGR_PERPLL_MISC */
    volatile ALT_CLKMGR_PERPLL_EMAC0CLK_t         emac0clk;           /* ALT_CLKMGR_PERPLL_EMAC0CLK */
    volatile ALT_CLKMGR_PERPLL_EMAC1CLK_t         emac1clk;           /* ALT_CLKMGR_PERPLL_EMAC1CLK */
    volatile ALT_CLKMGR_PERPLL_PERQSPICLK_t       perqspiclk;         /* ALT_CLKMGR_PERPLL_PERQSPICLK */
    volatile ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK_t  pernandsdmmcclk;    /* ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK */
    volatile ALT_CLKMGR_PERPLL_PERBASECLK_t       perbaseclk;         /* ALT_CLKMGR_PERPLL_PERBASECLK */
    volatile ALT_CLKMGR_PERPLL_S2FUSER1CLK_t      s2fuser1clk;        /* ALT_CLKMGR_PERPLL_S2FUSER1CLK */
    volatile ALT_CLKMGR_PERPLL_EN_t               en;                 /* ALT_CLKMGR_PERPLL_EN */
    volatile ALT_CLKMGR_PERPLL_DIV_t              div;                /* ALT_CLKMGR_PERPLL_DIV */
    volatile ALT_CLKMGR_PERPLL_GPIODIV_t          gpiodiv;            /* ALT_CLKMGR_PERPLL_GPIODIV */
    volatile ALT_CLKMGR_PERPLL_SRC_t              src;                /* ALT_CLKMGR_PERPLL_SRC */
    volatile ALT_CLKMGR_PERPLL_STAT_t             stat;               /* ALT_CLKMGR_PERPLL_STAT */
    volatile uint32_t                             _pad_0x34_0x40[3];  /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_CLKMGR_PERPLL. */
typedef volatile struct ALT_CLKMGR_PERPLL_s  ALT_CLKMGR_PERPLL_t;
/* The struct declaration for the raw register contents of register group ALT_CLKMGR_PERPLL. */
struct ALT_CLKMGR_PERPLL_raw_s
{
    volatile uint32_t  vco;                /* ALT_CLKMGR_PERPLL_VCO */
    volatile uint32_t  misc;               /* ALT_CLKMGR_PERPLL_MISC */
    volatile uint32_t  emac0clk;           /* ALT_CLKMGR_PERPLL_EMAC0CLK */
    volatile uint32_t  emac1clk;           /* ALT_CLKMGR_PERPLL_EMAC1CLK */
    volatile uint32_t  perqspiclk;         /* ALT_CLKMGR_PERPLL_PERQSPICLK */
    volatile uint32_t  pernandsdmmcclk;    /* ALT_CLKMGR_PERPLL_PERNANDSDMMCCLK */
    volatile uint32_t  perbaseclk;         /* ALT_CLKMGR_PERPLL_PERBASECLK */
    volatile uint32_t  s2fuser1clk;        /* ALT_CLKMGR_PERPLL_S2FUSER1CLK */
    volatile uint32_t  en;                 /* ALT_CLKMGR_PERPLL_EN */
    volatile uint32_t  div;                /* ALT_CLKMGR_PERPLL_DIV */
    volatile uint32_t  gpiodiv;            /* ALT_CLKMGR_PERPLL_GPIODIV */
    volatile uint32_t  src;                /* ALT_CLKMGR_PERPLL_SRC */
    volatile uint32_t  stat;               /* ALT_CLKMGR_PERPLL_STAT */
    volatile uint32_t  _pad_0x34_0x40[3];  /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_CLKMGR_PERPLL. */
typedef volatile struct ALT_CLKMGR_PERPLL_raw_s  ALT_CLKMGR_PERPLL_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : SDRAM PLL Group - ALT_CLKMGR_SDRPLL
 * SDRAM PLL Group
 * 
 * Contains registers with settings for the SDRAM PLL.
 * 
 */
/*
 * Register : SDRAM PLL VCO Control Register - vco
 * 
 * Contains settings that control the SDRAM PLL VCO. The VCO output frequency is
 * the input frequency multiplied by the numerator (M+1) and divided by the
 * denominator (N+1).
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                    
 * :--------|:-------|:------|:--------------------------------
 *  [0]     | RW     | 0x1   | BG PWRDN                       
 *  [1]     | RW     | 0x0   | Enable                         
 *  [2]     | RW     | 0x1   | Power down                     
 *  [15:3]  | RW     | 0x1   | Numerator (M)                  
 *  [21:16] | RW     | 0x1   | Denominator (N)                
 *  [23:22] | RW     | 0x0   | Clock Source                   
 *  [24]    | RW     | 0x0   | SDRAM All Output Counter Reset 
 *  [30:25] | RW     | 0x0   | Output Counter Reset           
 *  [31]    | RW     | 0x1   | External Regulator Input Select
 * 
 */
/*
 * Field : BG PWRDN - bgpwrdn
 * 
 * If '1', powers down bandgap. If '0', bandgap is not power down.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_VCO_BGPWRDN register field. */
#define ALT_CLKMGR_SDRPLL_VCO_BGPWRDN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_VCO_BGPWRDN register field. */
#define ALT_CLKMGR_SDRPLL_VCO_BGPWRDN_MSB        0
/* The width in bits of the ALT_CLKMGR_SDRPLL_VCO_BGPWRDN register field. */
#define ALT_CLKMGR_SDRPLL_VCO_BGPWRDN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_SDRPLL_VCO_BGPWRDN register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_BGPWRDN_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_SDRPLL_VCO_BGPWRDN register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_BGPWRDN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_SDRPLL_VCO_BGPWRDN register field. */
#define ALT_CLKMGR_SDRPLL_VCO_BGPWRDN_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_VCO_BGPWRDN field value from a register. */
#define ALT_CLKMGR_SDRPLL_VCO_BGPWRDN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_SDRPLL_VCO_BGPWRDN register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_VCO_BGPWRDN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Enable - en
 * 
 * If '1', VCO is enabled. If '0', VCO is in reset.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_VCO_EN register field. */
#define ALT_CLKMGR_SDRPLL_VCO_EN_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_VCO_EN register field. */
#define ALT_CLKMGR_SDRPLL_VCO_EN_MSB        1
/* The width in bits of the ALT_CLKMGR_SDRPLL_VCO_EN register field. */
#define ALT_CLKMGR_SDRPLL_VCO_EN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_SDRPLL_VCO_EN register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_EN_SET_MSK    0x00000002
/* The mask used to clear the ALT_CLKMGR_SDRPLL_VCO_EN register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_EN_CLR_MSK    0xfffffffd
/* The reset value of the ALT_CLKMGR_SDRPLL_VCO_EN register field. */
#define ALT_CLKMGR_SDRPLL_VCO_EN_RESET      0x0
/* Extracts the ALT_CLKMGR_SDRPLL_VCO_EN field value from a register. */
#define ALT_CLKMGR_SDRPLL_VCO_EN_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_CLKMGR_SDRPLL_VCO_EN register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_VCO_EN_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Power down - pwrdn
 * 
 * If '1', power down analog circuitry. If '0', analog circuitry not powered down.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_VCO_PWRDN register field. */
#define ALT_CLKMGR_SDRPLL_VCO_PWRDN_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_VCO_PWRDN register field. */
#define ALT_CLKMGR_SDRPLL_VCO_PWRDN_MSB        2
/* The width in bits of the ALT_CLKMGR_SDRPLL_VCO_PWRDN register field. */
#define ALT_CLKMGR_SDRPLL_VCO_PWRDN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_SDRPLL_VCO_PWRDN register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_PWRDN_SET_MSK    0x00000004
/* The mask used to clear the ALT_CLKMGR_SDRPLL_VCO_PWRDN register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_PWRDN_CLR_MSK    0xfffffffb
/* The reset value of the ALT_CLKMGR_SDRPLL_VCO_PWRDN register field. */
#define ALT_CLKMGR_SDRPLL_VCO_PWRDN_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_VCO_PWRDN field value from a register. */
#define ALT_CLKMGR_SDRPLL_VCO_PWRDN_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_CLKMGR_SDRPLL_VCO_PWRDN register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_VCO_PWRDN_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Numerator (M) - numer
 * 
 * Numerator in VCO output frequency equation. For incremental frequency change, if
 * the new value lead to less than 20% of the frequency change, this value can be
 * changed without resetting the PLL. The Numerator and Denominator can not be
 * changed at the same time for incremental frequency changed.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_VCO_NUMER register field. */
#define ALT_CLKMGR_SDRPLL_VCO_NUMER_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_VCO_NUMER register field. */
#define ALT_CLKMGR_SDRPLL_VCO_NUMER_MSB        15
/* The width in bits of the ALT_CLKMGR_SDRPLL_VCO_NUMER register field. */
#define ALT_CLKMGR_SDRPLL_VCO_NUMER_WIDTH      13
/* The mask used to set the ALT_CLKMGR_SDRPLL_VCO_NUMER register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_NUMER_SET_MSK    0x0000fff8
/* The mask used to clear the ALT_CLKMGR_SDRPLL_VCO_NUMER register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_NUMER_CLR_MSK    0xffff0007
/* The reset value of the ALT_CLKMGR_SDRPLL_VCO_NUMER register field. */
#define ALT_CLKMGR_SDRPLL_VCO_NUMER_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_VCO_NUMER field value from a register. */
#define ALT_CLKMGR_SDRPLL_VCO_NUMER_GET(value) (((value) & 0x0000fff8) >> 3)
/* Produces a ALT_CLKMGR_SDRPLL_VCO_NUMER register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_VCO_NUMER_SET(value) (((value) << 3) & 0x0000fff8)

/*
 * Field : Denominator (N) - denom
 * 
 * Denominator in VCO output frequency equation. For incremental frequency change,
 * if the new value lead to less than 20% of the frequency change, this value can
 * be changed without resetting the PLL. The Numerator and Denominator can not be
 * changed at the same time for incremental frequency changed.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_VCO_DENOM register field. */
#define ALT_CLKMGR_SDRPLL_VCO_DENOM_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_VCO_DENOM register field. */
#define ALT_CLKMGR_SDRPLL_VCO_DENOM_MSB        21
/* The width in bits of the ALT_CLKMGR_SDRPLL_VCO_DENOM register field. */
#define ALT_CLKMGR_SDRPLL_VCO_DENOM_WIDTH      6
/* The mask used to set the ALT_CLKMGR_SDRPLL_VCO_DENOM register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_DENOM_SET_MSK    0x003f0000
/* The mask used to clear the ALT_CLKMGR_SDRPLL_VCO_DENOM register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_DENOM_CLR_MSK    0xffc0ffff
/* The reset value of the ALT_CLKMGR_SDRPLL_VCO_DENOM register field. */
#define ALT_CLKMGR_SDRPLL_VCO_DENOM_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_VCO_DENOM field value from a register. */
#define ALT_CLKMGR_SDRPLL_VCO_DENOM_GET(value) (((value) & 0x003f0000) >> 16)
/* Produces a ALT_CLKMGR_SDRPLL_VCO_DENOM register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_VCO_DENOM_SET(value) (((value) << 16) & 0x003f0000)

/*
 * Field : Clock Source - ssrc
 * 
 * Controls the VCO input clock source. The PLL must by bypassed to eosc1_clk
 * before changing this field.
 * 
 * Qsys and user documenation refer to f2s_sdram_ref_clk as f2h_sdram_ref_clk.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                       | Value | Description      
 * :-------------------------------------------|:------|:------------------
 *  ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC1         | 0x0   | eosc1_clk        
 *  ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC2         | 0x1   | eosc2_clk        
 *  ALT_CLKMGR_SDRPLL_VCO_SSRC_E_F2S_SDRAM_REF | 0x2   | f2s_sdram_ref_clk
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_SDRPLL_VCO_SSRC
 * 
 * eosc1_clk
 */
#define ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC1          0x0
/*
 * Enumerated value for register field ALT_CLKMGR_SDRPLL_VCO_SSRC
 * 
 * eosc2_clk
 */
#define ALT_CLKMGR_SDRPLL_VCO_SSRC_E_EOSC2          0x1
/*
 * Enumerated value for register field ALT_CLKMGR_SDRPLL_VCO_SSRC
 * 
 * f2s_sdram_ref_clk
 */
#define ALT_CLKMGR_SDRPLL_VCO_SSRC_E_F2S_SDRAM_REF  0x2

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_VCO_SSRC register field. */
#define ALT_CLKMGR_SDRPLL_VCO_SSRC_LSB        22
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_VCO_SSRC register field. */
#define ALT_CLKMGR_SDRPLL_VCO_SSRC_MSB        23
/* The width in bits of the ALT_CLKMGR_SDRPLL_VCO_SSRC register field. */
#define ALT_CLKMGR_SDRPLL_VCO_SSRC_WIDTH      2
/* The mask used to set the ALT_CLKMGR_SDRPLL_VCO_SSRC register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_SSRC_SET_MSK    0x00c00000
/* The mask used to clear the ALT_CLKMGR_SDRPLL_VCO_SSRC register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_SSRC_CLR_MSK    0xff3fffff
/* The reset value of the ALT_CLKMGR_SDRPLL_VCO_SSRC register field. */
#define ALT_CLKMGR_SDRPLL_VCO_SSRC_RESET      0x0
/* Extracts the ALT_CLKMGR_SDRPLL_VCO_SSRC field value from a register. */
#define ALT_CLKMGR_SDRPLL_VCO_SSRC_GET(value) (((value) & 0x00c00000) >> 22)
/* Produces a ALT_CLKMGR_SDRPLL_VCO_SSRC register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_VCO_SSRC_SET(value) (((value) << 22) & 0x00c00000)

/*
 * Field : SDRAM All Output Counter Reset - outresetall
 * 
 * Before releasing Bypass, All Output Counter Reset must be set and cleared by
 * software for correct clock operation.
 * 
 * If '1', Reset phase multiplexer and output counter state. So that after the
 * assertion all the clocks output are start from rising edge align.
 * 
 * If '0', phase multiplexer and output counter state not reset and no change to
 * the phase of the clock outputs.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL register field. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL register field. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL_MSB        24
/* The width in bits of the ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL register field. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL_WIDTH      1
/* The mask used to set the ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL_SET_MSK    0x01000000
/* The mask used to clear the ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL_CLR_MSK    0xfeffffff
/* The reset value of the ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL register field. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL_RESET      0x0
/* Extracts the ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL field value from a register. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL_GET(value) (((value) & 0x01000000) >> 24)
/* Produces a ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRSTALL_SET(value) (((value) << 24) & 0x01000000)

/*
 * Field : Output Counter Reset - outreset
 * 
 * Resets the individual PLL output counter.
 * 
 * For software to change the PLL output counter without producing glitches on the
 * respective clock, SW must set the VCO register respective Output Counter Reset
 * bit. Software then polls the respective Output Counter Reset Acknowledge bit in
 * the Output Counter Reset Ack Status Register. Software then writes the
 * appropriate counter register, and then clears the respective VCO register Output
 * Counter Reset bit.
 * 
 * LSB 'outreset[0]' corresponds to PLL output clock C0, etc.
 * 
 * If set to '1', reset output divider, no clock output from counter.
 * 
 * If set to '0', counter is not reset.
 * 
 * The reset value of this bit is applied on a cold reset; warm reset has no affect
 * on this bit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_VCO_OUTRST register field. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRST_LSB        25
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_VCO_OUTRST register field. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRST_MSB        30
/* The width in bits of the ALT_CLKMGR_SDRPLL_VCO_OUTRST register field. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRST_WIDTH      6
/* The mask used to set the ALT_CLKMGR_SDRPLL_VCO_OUTRST register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRST_SET_MSK    0x7e000000
/* The mask used to clear the ALT_CLKMGR_SDRPLL_VCO_OUTRST register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRST_CLR_MSK    0x81ffffff
/* The reset value of the ALT_CLKMGR_SDRPLL_VCO_OUTRST register field. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRST_RESET      0x0
/* Extracts the ALT_CLKMGR_SDRPLL_VCO_OUTRST field value from a register. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRST_GET(value) (((value) & 0x7e000000) >> 25)
/* Produces a ALT_CLKMGR_SDRPLL_VCO_OUTRST register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_VCO_OUTRST_SET(value) (((value) << 25) & 0x7e000000)

/*
 * Field : External Regulator Input Select - regextsel
 * 
 * If set to '1', the external regulator is selected for the PLL.
 * 
 * If set to '0', the internal regulator is slected.
 * 
 * It is strongly recommended to select the external regulator while the PLL is not
 * enabled (in reset), and  then disable the external regulater once the PLL
 * becomes enabled.  Software should simulateously update the 'Enable' bit and the
 * 'External Regulator Input Select' in the same write access to the VCO register.
 * When the 'Enable' bit is clear, the 'External Regulator Input Select' should be
 * set, and vice versa.
 * 
 * The reset value of this bit is applied on a cold reset; warm reset has no affect
 * on this bit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL register field. */
#define ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL_LSB        31
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL register field. */
#define ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL_MSB        31
/* The width in bits of the ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL register field. */
#define ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL_WIDTH      1
/* The mask used to set the ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL_SET_MSK    0x80000000
/* The mask used to clear the ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL register field value. */
#define ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL_CLR_MSK    0x7fffffff
/* The reset value of the ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL register field. */
#define ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL field value from a register. */
#define ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL_GET(value) (((value) & 0x80000000) >> 31)
/* Produces a ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_VCO_REGEXTSEL_SET(value) (((value) << 31) & 0x80000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_SDRPLL_VCO.
 */
struct ALT_CLKMGR_SDRPLL_VCO_s
{
    uint32_t  bgpwrdn     :  1;  /* BG PWRDN */
    uint32_t  en          :  1;  /* Enable */
    uint32_t  pwrdn       :  1;  /* Power down */
    uint32_t  numer       : 13;  /* Numerator (M) */
    uint32_t  denom       :  6;  /* Denominator (N) */
    uint32_t  ssrc        :  2;  /* Clock Source */
    uint32_t  outresetall :  1;  /* SDRAM All Output Counter Reset */
    uint32_t  outreset    :  6;  /* Output Counter Reset */
    uint32_t  regextsel   :  1;  /* External Regulator Input Select */
};

/* The typedef declaration for register ALT_CLKMGR_SDRPLL_VCO. */
typedef volatile struct ALT_CLKMGR_SDRPLL_VCO_s  ALT_CLKMGR_SDRPLL_VCO_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_SDRPLL_VCO register from the beginning of the component. */
#define ALT_CLKMGR_SDRPLL_VCO_OFST        0x0

/*
 * Register : SDRAM PLL VCO Advanced Control Register - ctrl
 * 
 * Contains VCO control signals and other PLL control signals need to be
 * controllable through register.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                  
 * :--------|:-------|:------|:------------------------------
 *  [0]     | RW     | 0x0   | Loop Bandwidth Adjust Enabled
 *  [12:1]  | RW     | 0x1   | Loop Bandwidth Adjust        
 *  [13]    | RW     | 0x0   | Fast Locking Enable          
 *  [14]    | RW     | 0x1   | Saturation Enable            
 *  [31:15] | ???    | 0x0   | *UNDEFINED*                  
 * 
 */
/*
 * Field : Loop Bandwidth Adjust Enabled - bwadjen
 * 
 * If set to 1, the Loop Bandwidth Adjust value comes from the Loop Bandwidth
 * Adjust field.
 * 
 * If set to 0, the Loop Bandwidth Adjust value equals the M field divided by 2
 * value of the VCO Control Register.  The M divided by 2 is the upper 12 bits
 * (12:1) of the M field in the VCO register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_CTL_BWADJEN register field. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJEN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_CTL_BWADJEN register field. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJEN_MSB        0
/* The width in bits of the ALT_CLKMGR_SDRPLL_CTL_BWADJEN register field. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJEN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_SDRPLL_CTL_BWADJEN register field value. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJEN_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_SDRPLL_CTL_BWADJEN register field value. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJEN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_SDRPLL_CTL_BWADJEN register field. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJEN_RESET      0x0
/* Extracts the ALT_CLKMGR_SDRPLL_CTL_BWADJEN field value from a register. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJEN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_SDRPLL_CTL_BWADJEN register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJEN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Loop Bandwidth Adjust - bwadj
 * 
 * Provides Loop Bandwidth Adjust value.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_CTL_BWADJ register field. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJ_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_CTL_BWADJ register field. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJ_MSB        12
/* The width in bits of the ALT_CLKMGR_SDRPLL_CTL_BWADJ register field. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJ_WIDTH      12
/* The mask used to set the ALT_CLKMGR_SDRPLL_CTL_BWADJ register field value. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJ_SET_MSK    0x00001ffe
/* The mask used to clear the ALT_CLKMGR_SDRPLL_CTL_BWADJ register field value. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJ_CLR_MSK    0xffffe001
/* The reset value of the ALT_CLKMGR_SDRPLL_CTL_BWADJ register field. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJ_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_CTL_BWADJ field value from a register. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJ_GET(value) (((value) & 0x00001ffe) >> 1)
/* Produces a ALT_CLKMGR_SDRPLL_CTL_BWADJ register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_CTL_BWADJ_SET(value) (((value) << 1) & 0x00001ffe)

/*
 * Field : Fast Locking Enable - fasten
 * 
 * Enables fast locking circuit.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_CTL_FASTEN register field. */
#define ALT_CLKMGR_SDRPLL_CTL_FASTEN_LSB        13
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_CTL_FASTEN register field. */
#define ALT_CLKMGR_SDRPLL_CTL_FASTEN_MSB        13
/* The width in bits of the ALT_CLKMGR_SDRPLL_CTL_FASTEN register field. */
#define ALT_CLKMGR_SDRPLL_CTL_FASTEN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_SDRPLL_CTL_FASTEN register field value. */
#define ALT_CLKMGR_SDRPLL_CTL_FASTEN_SET_MSK    0x00002000
/* The mask used to clear the ALT_CLKMGR_SDRPLL_CTL_FASTEN register field value. */
#define ALT_CLKMGR_SDRPLL_CTL_FASTEN_CLR_MSK    0xffffdfff
/* The reset value of the ALT_CLKMGR_SDRPLL_CTL_FASTEN register field. */
#define ALT_CLKMGR_SDRPLL_CTL_FASTEN_RESET      0x0
/* Extracts the ALT_CLKMGR_SDRPLL_CTL_FASTEN field value from a register. */
#define ALT_CLKMGR_SDRPLL_CTL_FASTEN_GET(value) (((value) & 0x00002000) >> 13)
/* Produces a ALT_CLKMGR_SDRPLL_CTL_FASTEN register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_CTL_FASTEN_SET(value) (((value) << 13) & 0x00002000)

/*
 * Field : Saturation Enable - saten
 * 
 * Enables saturation behavior.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_CTL_SATEN register field. */
#define ALT_CLKMGR_SDRPLL_CTL_SATEN_LSB        14
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_CTL_SATEN register field. */
#define ALT_CLKMGR_SDRPLL_CTL_SATEN_MSB        14
/* The width in bits of the ALT_CLKMGR_SDRPLL_CTL_SATEN register field. */
#define ALT_CLKMGR_SDRPLL_CTL_SATEN_WIDTH      1
/* The mask used to set the ALT_CLKMGR_SDRPLL_CTL_SATEN register field value. */
#define ALT_CLKMGR_SDRPLL_CTL_SATEN_SET_MSK    0x00004000
/* The mask used to clear the ALT_CLKMGR_SDRPLL_CTL_SATEN register field value. */
#define ALT_CLKMGR_SDRPLL_CTL_SATEN_CLR_MSK    0xffffbfff
/* The reset value of the ALT_CLKMGR_SDRPLL_CTL_SATEN register field. */
#define ALT_CLKMGR_SDRPLL_CTL_SATEN_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_CTL_SATEN field value from a register. */
#define ALT_CLKMGR_SDRPLL_CTL_SATEN_GET(value) (((value) & 0x00004000) >> 14)
/* Produces a ALT_CLKMGR_SDRPLL_CTL_SATEN register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_CTL_SATEN_SET(value) (((value) << 14) & 0x00004000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_SDRPLL_CTL.
 */
struct ALT_CLKMGR_SDRPLL_CTL_s
{
    uint32_t  bwadjen :  1;  /* Loop Bandwidth Adjust Enabled */
    uint32_t  bwadj   : 12;  /* Loop Bandwidth Adjust */
    uint32_t  fasten  :  1;  /* Fast Locking Enable */
    uint32_t  saten   :  1;  /* Saturation Enable */
    uint32_t          : 17;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_SDRPLL_CTL. */
typedef volatile struct ALT_CLKMGR_SDRPLL_CTL_s  ALT_CLKMGR_SDRPLL_CTL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_SDRPLL_CTL register from the beginning of the component. */
#define ALT_CLKMGR_SDRPLL_CTL_OFST        0x4

/*
 * Register : SDRAM PLL C0 Control Register for Clock ddr_dqs_clk - ddrdqsclk
 * 
 * Contains settings that control clock ddr_dqs_clk generated from the C0 output of
 * the SDRAM PLL.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description
 * :--------|:-------|:------|:------------
 *  [8:0]   | RW     | 0x1   | Counter    
 *  [20:9]  | RW     | 0x0   | Phase Shift
 *  [31:21] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT register field value. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT register field value. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT field value from a register. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

/*
 * Field : Phase Shift - phase
 * 
 * Increment the phase of the VCO output by the value in this field multiplied by
 * 45 degrees. The accumulated phase shift is the total shifted amount since the
 * last assertion of the 'SDRAM All Output Divider Reset' bit in the SDRAM vco
 * control register. In order to guarantee the phase shift to a known value, 'SDRAM
 * clocks output phase align' bit should be asserted before programming this field.
 * 
 * This field is only writeable by SW when it is zero.  HW updates this field in
 * real time as the phase adjustment is being made.   SW may poll this field
 * waiting for zero indicating the phase adjustment has completed by HW.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE_MSB        20
/* The width in bits of the ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE_WIDTH      12
/* The mask used to set the ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE register field value. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE_SET_MSK    0x001ffe00
/* The mask used to clear the ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE register field value. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE_CLR_MSK    0xffe001ff
/* The reset value of the ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE_RESET      0x0
/* Extracts the ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE field value from a register. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE_GET(value) (((value) & 0x001ffe00) >> 9)
/* Produces a ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_PHASE_SET(value) (((value) << 9) & 0x001ffe00)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_SDRPLL_DDRDQSCLK.
 */
struct ALT_CLKMGR_SDRPLL_DDRDQSCLK_s
{
    uint32_t  cnt   :  9;  /* Counter */
    uint32_t  phase : 12;  /* Phase Shift */
    uint32_t        : 11;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_SDRPLL_DDRDQSCLK. */
typedef volatile struct ALT_CLKMGR_SDRPLL_DDRDQSCLK_s  ALT_CLKMGR_SDRPLL_DDRDQSCLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_SDRPLL_DDRDQSCLK register from the beginning of the component. */
#define ALT_CLKMGR_SDRPLL_DDRDQSCLK_OFST        0x8

/*
 * Register : SDRAM PLL C1 Control Register for Clock ddr_2x_dqs_clk - ddr2xdqsclk
 * 
 * Contains settings that control clock ddr_2x_dqs_clk generated from the C1 output
 * of the SDRAM PLL.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description
 * :--------|:-------|:------|:------------
 *  [8:0]   | RW     | 0x1   | Counter    
 *  [20:9]  | RW     | 0x0   | Phase Shift
 *  [31:21] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT register field value. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT register field value. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT field value from a register. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

/*
 * Field : Phase Shift - phase
 * 
 * Increment the phase of the VCO output by the value in this field multiplied by
 * 45 degrees. The accumulated phase shift is the total shifted amount since the
 * last assertion of the 'SDRAM All Output Divider Reset' bit in the SDRAM vco
 * control register. In order to guarantee the phase shift to a known value, 'SDRAM
 * clocks output phase align' bit should be asserted before programming this field.
 * 
 * This field is only writeable by SW when it is zero.  HW updates this field in
 * real time as the phase adjustment is being made.   SW may poll this field
 * waiting for zero indicating the phase adjustment has completed by HW.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE_MSB        20
/* The width in bits of the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE_WIDTH      12
/* The mask used to set the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE register field value. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE_SET_MSK    0x001ffe00
/* The mask used to clear the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE register field value. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE_CLR_MSK    0xffe001ff
/* The reset value of the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE_RESET      0x0
/* Extracts the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE field value from a register. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE_GET(value) (((value) & 0x001ffe00) >> 9)
/* Produces a ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_PHASE_SET(value) (((value) << 9) & 0x001ffe00)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_SDRPLL_DDR2XDQSCLK.
 */
struct ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_s
{
    uint32_t  cnt   :  9;  /* Counter */
    uint32_t  phase : 12;  /* Phase Shift */
    uint32_t        : 11;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_SDRPLL_DDR2XDQSCLK. */
typedef volatile struct ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_s  ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_SDRPLL_DDR2XDQSCLK register from the beginning of the component. */
#define ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_OFST        0xc

/*
 * Register : SDRAM PLL C2 Control Register for Clock ddr_dq_clk - ddrdqclk
 * 
 * Contains settings that control clock ddr_dq_clk generated from the C2 output of
 * the SDRAM PLL.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description
 * :--------|:-------|:------|:------------
 *  [8:0]   | RW     | 0x1   | Counter    
 *  [20:9]  | RW     | 0x0   | Phase Shift
 *  [31:21] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT register field value. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT register field value. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT field value from a register. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

/*
 * Field : Phase Shift - phase
 * 
 * Increment the phase of the VCO output by the value in this field multiplied by
 * 45 degrees. The accumulated phase shift is the total shifted amount since the
 * last assertion of the 'SDRAM All Output Divider Reset' bit in the SDRAM vco
 * control register. In order to guarantee the phase shift to a known value, 'SDRAM
 * clocks output phase align' bit should be asserted before programming this field.
 * 
 * This field is only writeable by SW when it is zero.  HW updates this field in
 * real time as the phase adjustment is being made.   SW may poll this field
 * waiting for zero indicating the phase adjustment has completed by HW.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE_MSB        20
/* The width in bits of the ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE_WIDTH      12
/* The mask used to set the ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE register field value. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE_SET_MSK    0x001ffe00
/* The mask used to clear the ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE register field value. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE_CLR_MSK    0xffe001ff
/* The reset value of the ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE_RESET      0x0
/* Extracts the ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE field value from a register. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE_GET(value) (((value) & 0x001ffe00) >> 9)
/* Produces a ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_PHASE_SET(value) (((value) << 9) & 0x001ffe00)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_SDRPLL_DDRDQCLK.
 */
struct ALT_CLKMGR_SDRPLL_DDRDQCLK_s
{
    uint32_t  cnt   :  9;  /* Counter */
    uint32_t  phase : 12;  /* Phase Shift */
    uint32_t        : 11;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_SDRPLL_DDRDQCLK. */
typedef volatile struct ALT_CLKMGR_SDRPLL_DDRDQCLK_s  ALT_CLKMGR_SDRPLL_DDRDQCLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_SDRPLL_DDRDQCLK register from the beginning of the component. */
#define ALT_CLKMGR_SDRPLL_DDRDQCLK_OFST        0x10

/*
 * Register : SDRAM PLL C5 Control Register for Clock s2f_user2_clk - s2fuser2clk
 * 
 * Contains settings that control clock s2f_user2_clk generated from the C5 output
 * of the SDRAM PLL.
 * 
 * Qsys and user documenation refer to s2f_user2_clk as h2f_user2_clk
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description
 * :--------|:-------|:------|:------------
 *  [8:0]   | RW     | 0x1   | Counter    
 *  [20:9]  | RW     | 0x0   | Phase Shift
 *  [31:21] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Counter - cnt
 * 
 * Divides the VCO frequency by the value+1 in this field.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT_MSB        8
/* The width in bits of the ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT_WIDTH      9
/* The mask used to set the ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT register field value. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT_SET_MSK    0x000001ff
/* The mask used to clear the ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT register field value. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT_CLR_MSK    0xfffffe00
/* The reset value of the ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT register field. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT field value from a register. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT_GET(value) (((value) & 0x000001ff) >> 0)
/* Produces a ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_CNT_SET(value) (((value) << 0) & 0x000001ff)

/*
 * Field : Phase Shift - phase
 * 
 * Increment the phase of the VCO output by the value in this field multiplied by
 * 45 degrees. The accumulated phase shift is the total shifted amount since the
 * last assertion of the 'SDRAM All Output Divider Reset' bit in the SDRAM vco
 * control register. In order to guarantee the phase shift to a known value, 'SDRAM
 * clocks output phase align' bit should be asserted before programming this field.
 * 
 * This field is only writeable by SW when it is zero.  HW updates this field in
 * real time as the phase adjustment is being made.   SW may poll this field
 * waiting for zero indicating the phase adjustment has completed by HW.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE_MSB        20
/* The width in bits of the ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE_WIDTH      12
/* The mask used to set the ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE register field value. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE_SET_MSK    0x001ffe00
/* The mask used to clear the ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE register field value. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE_CLR_MSK    0xffe001ff
/* The reset value of the ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE register field. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE_RESET      0x0
/* Extracts the ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE field value from a register. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE_GET(value) (((value) & 0x001ffe00) >> 9)
/* Produces a ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_PHASE_SET(value) (((value) << 9) & 0x001ffe00)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_SDRPLL_S2FUSER2CLK.
 */
struct ALT_CLKMGR_SDRPLL_S2FUSER2CLK_s
{
    uint32_t  cnt   :  9;  /* Counter */
    uint32_t  phase : 12;  /* Phase Shift */
    uint32_t        : 11;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_SDRPLL_S2FUSER2CLK. */
typedef volatile struct ALT_CLKMGR_SDRPLL_S2FUSER2CLK_s  ALT_CLKMGR_SDRPLL_S2FUSER2CLK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_SDRPLL_S2FUSER2CLK register from the beginning of the component. */
#define ALT_CLKMGR_SDRPLL_S2FUSER2CLK_OFST        0x14

/*
 * Register : Enable Register - en
 * 
 * Contains fields that control the SDRAM Clock Group enables generated from the
 * SDRAM PLL clock outputs.
 * 
 * 1: The clock is enabled.
 * 
 * 0: The clock is disabled.
 * 
 * Fields are only reset by a cold reset.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description          
 * :-------|:-------|:------|:----------------------
 *  [0]    | RW     | 0x1   | ddr_dqs_clk Enable   
 *  [1]    | RW     | 0x1   | ddr_2x_dqs_clk Enable
 *  [2]    | RW     | 0x1   | ddr_dq_clk Enable    
 *  [3]    | RW     | 0x1   | s2f_user2_clk Enable 
 *  [31:4] | ???    | 0x0   | *UNDEFINED*          
 * 
 */
/*
 * Field : ddr_dqs_clk Enable - ddrdqsclk
 * 
 * Enables clock ddr_dqs_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK_MSB        0
/* The width in bits of the ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK register field value. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK_SET_MSK    0x00000001
/* The mask used to clear the ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK register field value. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK_CLR_MSK    0xfffffffe
/* The reset value of the ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK field value from a register. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQSCLK_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : ddr_2x_dqs_clk Enable - ddr2xdqsclk
 * 
 * Enables clock ddr_2x_dqs_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK_MSB        1
/* The width in bits of the ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK register field value. */
#define ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK_SET_MSK    0x00000002
/* The mask used to clear the ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK register field value. */
#define ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK_CLR_MSK    0xfffffffd
/* The reset value of the ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK field value from a register. */
#define ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_EN_DDR2XDQSCLK_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : ddr_dq_clk Enable - ddrdqclk
 * 
 * Enables clock ddr_dq_clk output
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_EN_DDRDQCLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQCLK_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_EN_DDRDQCLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQCLK_MSB        2
/* The width in bits of the ALT_CLKMGR_SDRPLL_EN_DDRDQCLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQCLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_SDRPLL_EN_DDRDQCLK register field value. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQCLK_SET_MSK    0x00000004
/* The mask used to clear the ALT_CLKMGR_SDRPLL_EN_DDRDQCLK register field value. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQCLK_CLR_MSK    0xfffffffb
/* The reset value of the ALT_CLKMGR_SDRPLL_EN_DDRDQCLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQCLK_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_EN_DDRDQCLK field value from a register. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQCLK_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_CLKMGR_SDRPLL_EN_DDRDQCLK register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_EN_DDRDQCLK_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : s2f_user2_clk Enable - s2fuser2clk
 * 
 * Enables clock s2f_user2_clk output.
 * 
 * Qsys and user documenation refer to s2f_user2_clk as h2f_user2_clk.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK_MSB        3
/* The width in bits of the ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK_WIDTH      1
/* The mask used to set the ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK register field value. */
#define ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK_SET_MSK    0x00000008
/* The mask used to clear the ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK register field value. */
#define ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK_CLR_MSK    0xfffffff7
/* The reset value of the ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK register field. */
#define ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK_RESET      0x1
/* Extracts the ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK field value from a register. */
#define ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_EN_S2FUSER2CLK_SET(value) (((value) << 3) & 0x00000008)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_SDRPLL_EN.
 */
struct ALT_CLKMGR_SDRPLL_EN_s
{
    uint32_t  ddrdqsclk   :  1;  /* ddr_dqs_clk Enable */
    uint32_t  ddr2xdqsclk :  1;  /* ddr_2x_dqs_clk Enable */
    uint32_t  ddrdqclk    :  1;  /* ddr_dq_clk Enable */
    uint32_t  s2fuser2clk :  1;  /* s2f_user2_clk Enable */
    uint32_t              : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_SDRPLL_EN. */
typedef volatile struct ALT_CLKMGR_SDRPLL_EN_s  ALT_CLKMGR_SDRPLL_EN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_SDRPLL_EN register from the beginning of the component. */
#define ALT_CLKMGR_SDRPLL_EN_OFST        0x18

/*
 * Register : SDRAM PLL Output Counter Reset Ack Status Register - stat
 * 
 * Contains Output Clock Counter Reset acknowledge status.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                     
 * :-------|:-------|:------|:---------------------------------
 *  [5:0]  | R      | 0x0   | Output Counter Reset Acknowledge
 *  [31:6] | ???    | 0x0   | *UNDEFINED*                     
 * 
 */
/*
 * Field : Output Counter Reset Acknowledge - outresetack
 * 
 * These read only bits per PLL output indicate that the PLL has received the
 * Output Reset Counter request and has gracefully stopped the respective PLL
 * output clock.
 * 
 * For software to change the PLL output counter without producing glitches on the
 * respective clock, SW must set the VCO register respective Output Counter Reset
 * bit. Software then polls the respective Output Counter Reset Acknowledge bit in
 * the Output Counter Reset Ack Status Register. Software then writes the
 * appropriate counter register, and then clears the respective VCO register Output
 * Counter Reset bit.
 * 
 * The reset value of this bit is applied on a cold reset; warm reset has no affect
 * on this bit.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                       | Value | Description                         
 * :-------------------------------------------|:------|:-------------------------------------
 *  ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK_E_IDLE    | 0x0   | Idle                                
 *  ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK_E_ACK_RXD | 0x1   | Output Counter Acknowledge received.
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK
 * 
 * Idle
 */
#define ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK_E_IDLE     0x0
/*
 * Enumerated value for register field ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK
 * 
 * Output Counter Acknowledge received.
 */
#define ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK_E_ACK_RXD  0x1

/* The Least Significant Bit (LSB) position of the ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK register field. */
#define ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK register field. */
#define ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK_MSB        5
/* The width in bits of the ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK register field. */
#define ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK_WIDTH      6
/* The mask used to set the ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK register field value. */
#define ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK_SET_MSK    0x0000003f
/* The mask used to clear the ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK register field value. */
#define ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK_CLR_MSK    0xffffffc0
/* The reset value of the ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK register field. */
#define ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK_RESET      0x0
/* Extracts the ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK field value from a register. */
#define ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK_GET(value) (((value) & 0x0000003f) >> 0)
/* Produces a ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK register field value suitable for setting the register. */
#define ALT_CLKMGR_SDRPLL_STAT_OUTRSTACK_SET(value) (((value) << 0) & 0x0000003f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_CLKMGR_SDRPLL_STAT.
 */
struct ALT_CLKMGR_SDRPLL_STAT_s
{
    const uint32_t  outresetack :  6;  /* Output Counter Reset Acknowledge */
    uint32_t                    : 26;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_CLKMGR_SDRPLL_STAT. */
typedef volatile struct ALT_CLKMGR_SDRPLL_STAT_s  ALT_CLKMGR_SDRPLL_STAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_CLKMGR_SDRPLL_STAT register from the beginning of the component. */
#define ALT_CLKMGR_SDRPLL_STAT_OFST        0x1c

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_CLKMGR_SDRPLL.
 */
struct ALT_CLKMGR_SDRPLL_s
{
    volatile ALT_CLKMGR_SDRPLL_VCO_t          vco;          /* ALT_CLKMGR_SDRPLL_VCO */
    volatile ALT_CLKMGR_SDRPLL_CTL_t          ctrl;         /* ALT_CLKMGR_SDRPLL_CTL */
    volatile ALT_CLKMGR_SDRPLL_DDRDQSCLK_t    ddrdqsclk;    /* ALT_CLKMGR_SDRPLL_DDRDQSCLK */
    volatile ALT_CLKMGR_SDRPLL_DDR2XDQSCLK_t  ddr2xdqsclk;  /* ALT_CLKMGR_SDRPLL_DDR2XDQSCLK */
    volatile ALT_CLKMGR_SDRPLL_DDRDQCLK_t     ddrdqclk;     /* ALT_CLKMGR_SDRPLL_DDRDQCLK */
    volatile ALT_CLKMGR_SDRPLL_S2FUSER2CLK_t  s2fuser2clk;  /* ALT_CLKMGR_SDRPLL_S2FUSER2CLK */
    volatile ALT_CLKMGR_SDRPLL_EN_t           en;           /* ALT_CLKMGR_SDRPLL_EN */
    volatile ALT_CLKMGR_SDRPLL_STAT_t         stat;         /* ALT_CLKMGR_SDRPLL_STAT */
};

/* The typedef declaration for register group ALT_CLKMGR_SDRPLL. */
typedef volatile struct ALT_CLKMGR_SDRPLL_s  ALT_CLKMGR_SDRPLL_t;
/* The struct declaration for the raw register contents of register group ALT_CLKMGR_SDRPLL. */
struct ALT_CLKMGR_SDRPLL_raw_s
{
    volatile uint32_t  vco;          /* ALT_CLKMGR_SDRPLL_VCO */
    volatile uint32_t  ctrl;         /* ALT_CLKMGR_SDRPLL_CTL */
    volatile uint32_t  ddrdqsclk;    /* ALT_CLKMGR_SDRPLL_DDRDQSCLK */
    volatile uint32_t  ddr2xdqsclk;  /* ALT_CLKMGR_SDRPLL_DDR2XDQSCLK */
    volatile uint32_t  ddrdqclk;     /* ALT_CLKMGR_SDRPLL_DDRDQCLK */
    volatile uint32_t  s2fuser2clk;  /* ALT_CLKMGR_SDRPLL_S2FUSER2CLK */
    volatile uint32_t  en;           /* ALT_CLKMGR_SDRPLL_EN */
    volatile uint32_t  stat;         /* ALT_CLKMGR_SDRPLL_STAT */
};

/* The typedef declaration for the raw register contents of register group ALT_CLKMGR_SDRPLL. */
typedef volatile struct ALT_CLKMGR_SDRPLL_raw_s  ALT_CLKMGR_SDRPLL_raw_t;
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
 * The struct declaration for register group ALT_CLKMGR.
 */
struct ALT_CLKMGR_s
{
    volatile ALT_CLKMGR_CTL_t      ctrl;                 /* ALT_CLKMGR_CTL */
    volatile ALT_CLKMGR_BYPASS_t   bypass;               /* ALT_CLKMGR_BYPASS */
    volatile ALT_CLKMGR_INTER_t    inter;                /* ALT_CLKMGR_INTER */
    volatile ALT_CLKMGR_INTREN_t   intren;               /* ALT_CLKMGR_INTREN */
    volatile ALT_CLKMGR_DBCTL_t    dbctrl;               /* ALT_CLKMGR_DBCTL */
    volatile ALT_CLKMGR_STAT_t     stat;                 /* ALT_CLKMGR_STAT */
    volatile uint32_t              _pad_0x18_0x3f[10];   /* *UNDEFINED* */
    volatile ALT_CLKMGR_MAINPLL_t  mainpllgrp;           /* ALT_CLKMGR_MAINPLL */
    volatile ALT_CLKMGR_PERPLL_t   perpllgrp;            /* ALT_CLKMGR_PERPLL */
    volatile ALT_CLKMGR_SDRPLL_t   sdrpllgrp;            /* ALT_CLKMGR_SDRPLL */
    volatile uint32_t              _pad_0xe0_0x200[72];  /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_CLKMGR. */
typedef volatile struct ALT_CLKMGR_s  ALT_CLKMGR_t;
/* The struct declaration for the raw register contents of register group ALT_CLKMGR. */
struct ALT_CLKMGR_raw_s
{
    volatile uint32_t                  ctrl;                 /* ALT_CLKMGR_CTL */
    volatile uint32_t                  bypass;               /* ALT_CLKMGR_BYPASS */
    volatile uint32_t                  inter;                /* ALT_CLKMGR_INTER */
    volatile uint32_t                  intren;               /* ALT_CLKMGR_INTREN */
    volatile uint32_t                  dbctrl;               /* ALT_CLKMGR_DBCTL */
    volatile uint32_t                  stat;                 /* ALT_CLKMGR_STAT */
    volatile uint32_t                  _pad_0x18_0x3f[10];   /* *UNDEFINED* */
    volatile ALT_CLKMGR_MAINPLL_raw_t  mainpllgrp;           /* ALT_CLKMGR_MAINPLL */
    volatile ALT_CLKMGR_PERPLL_raw_t   perpllgrp;            /* ALT_CLKMGR_PERPLL */
    volatile ALT_CLKMGR_SDRPLL_raw_t   sdrpllgrp;            /* ALT_CLKMGR_SDRPLL */
    volatile uint32_t                  _pad_0xe0_0x200[72];  /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_CLKMGR. */
typedef volatile struct ALT_CLKMGR_raw_s  ALT_CLKMGR_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_CLKMGR_H__ */

