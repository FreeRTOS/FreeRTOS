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

/* Altera - ALT_L4WD */

#ifndef __ALTERA_ALT_L4WD_H__
#define __ALTERA_ALT_L4WD_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : L4 Watchdog Module - ALT_L4WD
 * L4 Watchdog Module
 * 
 * Registers in the L4 Watchdog module
 * 
 */
/*
 * Register : Control Register - wdt_cr
 * 
 * Contains fields that control operating functions.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description  
 * :-------|:-------|:------|:--------------
 *  [0]    | RW     | 0x0   | Enable       
 *  [1]    | RW     | 0x1   | Response Mode
 *  [31:2] | ???    | 0x0   | *UNDEFINED*  
 * 
 */
/*
 * Field : Enable - wdt_en
 * 
 * This bit is used to enable and disable the watchdog. When disabled, the counter
 * does not decrement. Thus, no interrupts or warm reset requests are generated.
 * Once this bit has been enabled, it can only be cleared only by resetting the
 * watchdog.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description      
 * :--------------------------|:------|:------------------
 *  ALT_L4WD_CR_WDT_EN_E_DISD | 0x0   | Watchdog disabled
 *  ALT_L4WD_CR_WDT_EN_E_END  | 0x1   | Watchdog enabled 
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_CR_WDT_EN
 * 
 * Watchdog disabled
 */
#define ALT_L4WD_CR_WDT_EN_E_DISD   0x0
/*
 * Enumerated value for register field ALT_L4WD_CR_WDT_EN
 * 
 * Watchdog enabled
 */
#define ALT_L4WD_CR_WDT_EN_E_END    0x1

/* The Least Significant Bit (LSB) position of the ALT_L4WD_CR_WDT_EN register field. */
#define ALT_L4WD_CR_WDT_EN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L4WD_CR_WDT_EN register field. */
#define ALT_L4WD_CR_WDT_EN_MSB        0
/* The width in bits of the ALT_L4WD_CR_WDT_EN register field. */
#define ALT_L4WD_CR_WDT_EN_WIDTH      1
/* The mask used to set the ALT_L4WD_CR_WDT_EN register field value. */
#define ALT_L4WD_CR_WDT_EN_SET_MSK    0x00000001
/* The mask used to clear the ALT_L4WD_CR_WDT_EN register field value. */
#define ALT_L4WD_CR_WDT_EN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L4WD_CR_WDT_EN register field. */
#define ALT_L4WD_CR_WDT_EN_RESET      0x0
/* Extracts the ALT_L4WD_CR_WDT_EN field value from a register. */
#define ALT_L4WD_CR_WDT_EN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L4WD_CR_WDT_EN register field value suitable for setting the register. */
#define ALT_L4WD_CR_WDT_EN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Response Mode - rmod
 * 
 * Selects the output response generated to a timeout.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description                                  
 * :--------------------------|:------|:----------------------------------------------
 *  ALT_L4WD_CR_RMOD_E_RST    | 0x0   | Generate a warm reset request                
 *  ALT_L4WD_CR_RMOD_E_IRQRST | 0x1   | First generate an interrupt, and if it is not
 * :                          |       | cleared by the time a second timeout occurs, 
 * :                          |       | then generate a warm reset request.          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_CR_RMOD
 * 
 * Generate a warm reset request
 */
#define ALT_L4WD_CR_RMOD_E_RST      0x0
/*
 * Enumerated value for register field ALT_L4WD_CR_RMOD
 * 
 * First generate an interrupt, and if it is not cleared by the time a second
 * timeout occurs, then generate a warm reset request.
 */
#define ALT_L4WD_CR_RMOD_E_IRQRST   0x1

/* The Least Significant Bit (LSB) position of the ALT_L4WD_CR_RMOD register field. */
#define ALT_L4WD_CR_RMOD_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_L4WD_CR_RMOD register field. */
#define ALT_L4WD_CR_RMOD_MSB        1
/* The width in bits of the ALT_L4WD_CR_RMOD register field. */
#define ALT_L4WD_CR_RMOD_WIDTH      1
/* The mask used to set the ALT_L4WD_CR_RMOD register field value. */
#define ALT_L4WD_CR_RMOD_SET_MSK    0x00000002
/* The mask used to clear the ALT_L4WD_CR_RMOD register field value. */
#define ALT_L4WD_CR_RMOD_CLR_MSK    0xfffffffd
/* The reset value of the ALT_L4WD_CR_RMOD register field. */
#define ALT_L4WD_CR_RMOD_RESET      0x1
/* Extracts the ALT_L4WD_CR_RMOD field value from a register. */
#define ALT_L4WD_CR_RMOD_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_L4WD_CR_RMOD register field value suitable for setting the register. */
#define ALT_L4WD_CR_RMOD_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L4WD_CR.
 */
struct ALT_L4WD_CR_s
{
    uint32_t  wdt_en :  1;  /* Enable */
    uint32_t  rmod   :  1;  /* Response Mode */
    uint32_t         : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L4WD_CR. */
typedef volatile struct ALT_L4WD_CR_s  ALT_L4WD_CR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L4WD_CR register from the beginning of the component. */
#define ALT_L4WD_CR_OFST        0x0
/* The address of the ALT_L4WD_CR register. */
#define ALT_L4WD_CR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L4WD_CR_OFST))

/*
 * Register : Timeout Range Register - wdt_torr
 * 
 * Contains fields that determine the watchdog timeout.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                      
 * :-------|:-------|:------|:----------------------------------
 *  [3:0]  | RW     | 0xf   | Timeout Period                   
 *  [7:4]  | RW     | 0xf   | Timeout Period for Initialization
 *  [31:8] | ???    | 0x0   | *UNDEFINED*                      
 * 
 */
/*
 * Field : Timeout Period - top
 * 
 * This field is used to select the timeout period from which the watchdog counter
 * restarts. A change of the timeout period takes effect only after the next
 * counter restart (kick). The timeout period (in clocks) is:
 * 
 * t = 2**(16 + top)
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                  
 * :----------------------------|:------|:------------------------------
 *  ALT_L4WD_TORR_TOP_E_TMO64K  | 0x0   | Timeout = 65536  osc1_clk    
 *  ALT_L4WD_TORR_TOP_E_TMO128K | 0x1   | Timeout = 131072 osc1_clk    
 *  ALT_L4WD_TORR_TOP_E_TMO256K | 0x2   | Timeout = 262144 osc1_clk    
 *  ALT_L4WD_TORR_TOP_E_TMO512K | 0x3   | Timeout = 524288 osc1_clk    
 *  ALT_L4WD_TORR_TOP_E_TMO1M   | 0x4   | Timeout = 1048576 osc1_clk   
 *  ALT_L4WD_TORR_TOP_E_TMO2M   | 0x5   | Timeout = 2097152 osc1_clk   
 *  ALT_L4WD_TORR_TOP_E_TMO4M   | 0x6   | Timeout = 4194304 osc1_clk   
 *  ALT_L4WD_TORR_TOP_E_TMO8M   | 0x7   | Timeout = 8388608 osc1_clk   
 *  ALT_L4WD_TORR_TOP_E_TMO16M  | 0x8   | Timeout = 16777216 osc1_clk  
 *  ALT_L4WD_TORR_TOP_E_TMO32M  | 0x9   | Timeout = 33554432 osc1_clk  
 *  ALT_L4WD_TORR_TOP_E_TMO64M  | 0xa   | Timeout = 67108864 osc1_clk  
 *  ALT_L4WD_TORR_TOP_E_TMO128M | 0xb   | Timeout = 134217728 osc1_clk 
 *  ALT_L4WD_TORR_TOP_E_TMO256M | 0xc   | Timeout = 268435456 osc1_clk 
 *  ALT_L4WD_TORR_TOP_E_TMO512M | 0xd   | Timeout = 536870912 osc1_clk 
 *  ALT_L4WD_TORR_TOP_E_TMO1G   | 0xe   | Timeout = 1073741824 osc1_clk
 *  ALT_L4WD_TORR_TOP_E_TMO2G   | 0xf   | Timeout = 2147483648 osc1_clk
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 65536  osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO64K  0x0
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 131072 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO128K 0x1
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 262144 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO256K 0x2
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 524288 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO512K 0x3
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 1048576 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO1M   0x4
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 2097152 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO2M   0x5
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 4194304 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO4M   0x6
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 8388608 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO8M   0x7
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 16777216 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO16M  0x8
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 33554432 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO32M  0x9
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 67108864 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO64M  0xa
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 134217728 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO128M 0xb
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 268435456 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO256M 0xc
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 536870912 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO512M 0xd
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 1073741824 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO1G   0xe
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP
 * 
 * Timeout = 2147483648 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_E_TMO2G   0xf

/* The Least Significant Bit (LSB) position of the ALT_L4WD_TORR_TOP register field. */
#define ALT_L4WD_TORR_TOP_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L4WD_TORR_TOP register field. */
#define ALT_L4WD_TORR_TOP_MSB        3
/* The width in bits of the ALT_L4WD_TORR_TOP register field. */
#define ALT_L4WD_TORR_TOP_WIDTH      4
/* The mask used to set the ALT_L4WD_TORR_TOP register field value. */
#define ALT_L4WD_TORR_TOP_SET_MSK    0x0000000f
/* The mask used to clear the ALT_L4WD_TORR_TOP register field value. */
#define ALT_L4WD_TORR_TOP_CLR_MSK    0xfffffff0
/* The reset value of the ALT_L4WD_TORR_TOP register field. */
#define ALT_L4WD_TORR_TOP_RESET      0xf
/* Extracts the ALT_L4WD_TORR_TOP field value from a register. */
#define ALT_L4WD_TORR_TOP_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_L4WD_TORR_TOP register field value suitable for setting the register. */
#define ALT_L4WD_TORR_TOP_SET(value) (((value) << 0) & 0x0000000f)

/*
 * Field : Timeout Period for Initialization - top_init
 * 
 * Used to select the timeout period that the watchdog counter restarts from for
 * the first counter restart (kick). This register should be written after reset
 * and before the watchdog is enabled. A change of the TOP_INIT is seen only once
 * the watchdog has been enabled, and any change after the first kick is not seen
 * as subsequent kicks use the period specified by the TOP bits. The timeout period
 * (in clocks) is:
 * 
 * t = 2**(16 + top_init)
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                  
 * :---------------------------------|:------|:------------------------------
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO64K  | 0x0   | Timeout = 65536  osc1_clk    
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO128K | 0x1   | Timeout = 131072 osc1_clk    
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO256K | 0x2   | Timeout = 262144 osc1_clk    
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO512K | 0x3   | Timeout = 524288 osc1_clk    
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO1M   | 0x4   | Timeout = 1048576 osc1_clk   
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO2M   | 0x5   | Timeout = 2097152 osc1_clk   
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO4M   | 0x6   | Timeout = 4194304 osc1_clk   
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO8M   | 0x7   | Timeout = 8388608 osc1_clk   
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO16M  | 0x8   | Timeout = 16777216 osc1_clk  
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO32M  | 0x9   | Timeout = 33554432 osc1_clk  
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO64M  | 0xa   | Timeout = 67108864 osc1_clk  
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO128M | 0xb   | Timeout = 134217728 osc1_clk 
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO256M | 0xc   | Timeout = 268435456 osc1_clk 
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO512M | 0xd   | Timeout = 536870912 osc1_clk 
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO1G   | 0xe   | Timeout = 1073741824 osc1_clk
 *  ALT_L4WD_TORR_TOP_INIT_E_TMO2G   | 0xf   | Timeout = 2147483648 osc1_clk
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 65536  osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO64K     0x0
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 131072 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO128K    0x1
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 262144 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO256K    0x2
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 524288 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO512K    0x3
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 1048576 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO1M      0x4
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 2097152 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO2M      0x5
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 4194304 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO4M      0x6
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 8388608 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO8M      0x7
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 16777216 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO16M     0x8
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 33554432 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO32M     0x9
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 67108864 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO64M     0xa
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 134217728 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO128M    0xb
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 268435456 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO256M    0xc
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 536870912 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO512M    0xd
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 1073741824 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO1G      0xe
/*
 * Enumerated value for register field ALT_L4WD_TORR_TOP_INIT
 * 
 * Timeout = 2147483648 osc1_clk
 */
#define ALT_L4WD_TORR_TOP_INIT_E_TMO2G      0xf

/* The Least Significant Bit (LSB) position of the ALT_L4WD_TORR_TOP_INIT register field. */
#define ALT_L4WD_TORR_TOP_INIT_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_L4WD_TORR_TOP_INIT register field. */
#define ALT_L4WD_TORR_TOP_INIT_MSB        7
/* The width in bits of the ALT_L4WD_TORR_TOP_INIT register field. */
#define ALT_L4WD_TORR_TOP_INIT_WIDTH      4
/* The mask used to set the ALT_L4WD_TORR_TOP_INIT register field value. */
#define ALT_L4WD_TORR_TOP_INIT_SET_MSK    0x000000f0
/* The mask used to clear the ALT_L4WD_TORR_TOP_INIT register field value. */
#define ALT_L4WD_TORR_TOP_INIT_CLR_MSK    0xffffff0f
/* The reset value of the ALT_L4WD_TORR_TOP_INIT register field. */
#define ALT_L4WD_TORR_TOP_INIT_RESET      0xf
/* Extracts the ALT_L4WD_TORR_TOP_INIT field value from a register. */
#define ALT_L4WD_TORR_TOP_INIT_GET(value) (((value) & 0x000000f0) >> 4)
/* Produces a ALT_L4WD_TORR_TOP_INIT register field value suitable for setting the register. */
#define ALT_L4WD_TORR_TOP_INIT_SET(value) (((value) << 4) & 0x000000f0)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L4WD_TORR.
 */
struct ALT_L4WD_TORR_s
{
    uint32_t  top      :  4;  /* Timeout Period */
    uint32_t  top_init :  4;  /* Timeout Period for Initialization */
    uint32_t           : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L4WD_TORR. */
typedef volatile struct ALT_L4WD_TORR_s  ALT_L4WD_TORR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L4WD_TORR register from the beginning of the component. */
#define ALT_L4WD_TORR_OFST        0x4
/* The address of the ALT_L4WD_TORR register. */
#define ALT_L4WD_TORR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L4WD_TORR_OFST))

/*
 * Register : Current Counter Value Register - wdt_ccvr
 * 
 * See Field Description
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset      | Description          
 * :-------|:-------|:-----------|:----------------------
 *  [31:0] | R      | 0x7fffffff | Current Counter Value
 * 
 */
/*
 * Field : Current Counter Value - wdt_ccvr
 * 
 * This register provides the current value of the internal counter.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_L4WD_CCVR_WDT_CCVR register field. */
#define ALT_L4WD_CCVR_WDT_CCVR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L4WD_CCVR_WDT_CCVR register field. */
#define ALT_L4WD_CCVR_WDT_CCVR_MSB        31
/* The width in bits of the ALT_L4WD_CCVR_WDT_CCVR register field. */
#define ALT_L4WD_CCVR_WDT_CCVR_WIDTH      32
/* The mask used to set the ALT_L4WD_CCVR_WDT_CCVR register field value. */
#define ALT_L4WD_CCVR_WDT_CCVR_SET_MSK    0xffffffff
/* The mask used to clear the ALT_L4WD_CCVR_WDT_CCVR register field value. */
#define ALT_L4WD_CCVR_WDT_CCVR_CLR_MSK    0x00000000
/* The reset value of the ALT_L4WD_CCVR_WDT_CCVR register field. */
#define ALT_L4WD_CCVR_WDT_CCVR_RESET      0x7fffffff
/* Extracts the ALT_L4WD_CCVR_WDT_CCVR field value from a register. */
#define ALT_L4WD_CCVR_WDT_CCVR_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_L4WD_CCVR_WDT_CCVR register field value suitable for setting the register. */
#define ALT_L4WD_CCVR_WDT_CCVR_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L4WD_CCVR.
 */
struct ALT_L4WD_CCVR_s
{
    const uint32_t  wdt_ccvr : 32;  /* Current Counter Value */
};

/* The typedef declaration for register ALT_L4WD_CCVR. */
typedef volatile struct ALT_L4WD_CCVR_s  ALT_L4WD_CCVR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L4WD_CCVR register from the beginning of the component. */
#define ALT_L4WD_CCVR_OFST        0x8
/* The address of the ALT_L4WD_CCVR register. */
#define ALT_L4WD_CCVR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L4WD_CCVR_OFST))

/*
 * Register : Counter Restart Register - wdt_crr
 * 
 * Restarts the watchdog.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description             
 * :-------|:-------|:------|:-------------------------
 *  [7:0]  | W      | 0x0   | Counter Restart Register
 *  [31:8] | ???    | 0x0   | *UNDEFINED*             
 * 
 */
/*
 * Field : Counter Restart Register - wdt_crr
 * 
 * This register is used to restart the watchdog counter. As a safety feature to
 * prevent accidental restarts, the kick value of 0x76 must be written. A restart
 * also clears the watchdog interrupt.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                        | Value | Description                             
 * :----------------------------|:------|:-----------------------------------------
 *  ALT_L4WD_CRR_WDT_CRR_E_KICK | 0x76  | Value to write to restart watchdog timer
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_CRR_WDT_CRR
 * 
 * Value to write to restart watchdog timer
 */
#define ALT_L4WD_CRR_WDT_CRR_E_KICK 0x76

/* The Least Significant Bit (LSB) position of the ALT_L4WD_CRR_WDT_CRR register field. */
#define ALT_L4WD_CRR_WDT_CRR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L4WD_CRR_WDT_CRR register field. */
#define ALT_L4WD_CRR_WDT_CRR_MSB        7
/* The width in bits of the ALT_L4WD_CRR_WDT_CRR register field. */
#define ALT_L4WD_CRR_WDT_CRR_WIDTH      8
/* The mask used to set the ALT_L4WD_CRR_WDT_CRR register field value. */
#define ALT_L4WD_CRR_WDT_CRR_SET_MSK    0x000000ff
/* The mask used to clear the ALT_L4WD_CRR_WDT_CRR register field value. */
#define ALT_L4WD_CRR_WDT_CRR_CLR_MSK    0xffffff00
/* The reset value of the ALT_L4WD_CRR_WDT_CRR register field. */
#define ALT_L4WD_CRR_WDT_CRR_RESET      0x0
/* Extracts the ALT_L4WD_CRR_WDT_CRR field value from a register. */
#define ALT_L4WD_CRR_WDT_CRR_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_L4WD_CRR_WDT_CRR register field value suitable for setting the register. */
#define ALT_L4WD_CRR_WDT_CRR_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L4WD_CRR.
 */
struct ALT_L4WD_CRR_s
{
    uint32_t  wdt_crr :  8;  /* Counter Restart Register */
    uint32_t          : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L4WD_CRR. */
typedef volatile struct ALT_L4WD_CRR_s  ALT_L4WD_CRR_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L4WD_CRR register from the beginning of the component. */
#define ALT_L4WD_CRR_OFST        0xc
/* The address of the ALT_L4WD_CRR register. */
#define ALT_L4WD_CRR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L4WD_CRR_OFST))

/*
 * Register : Interrupt Status Register. - wdt_stat
 * 
 * Provides interrupt status
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description     
 * :-------|:-------|:------|:-----------------
 *  [0]    | R      | 0x0   | Interrupt Status
 *  [31:1] | ???    | 0x0   | *UNDEFINED*     
 * 
 */
/*
 * Field : Interrupt Status - wdt_stat
 * 
 * Provides the interrupt status of the watchdog.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description          
 * :-------------------------------|:------|:----------------------
 *  ALT_L4WD_STAT_WDT_STAT_E_ACT   | 0x1   | Interrupt is active  
 *  ALT_L4WD_STAT_WDT_STAT_E_INACT | 0x0   | Interrupt is inactive
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_STAT_WDT_STAT
 * 
 * Interrupt is active
 */
#define ALT_L4WD_STAT_WDT_STAT_E_ACT    0x1
/*
 * Enumerated value for register field ALT_L4WD_STAT_WDT_STAT
 * 
 * Interrupt is inactive
 */
#define ALT_L4WD_STAT_WDT_STAT_E_INACT  0x0

/* The Least Significant Bit (LSB) position of the ALT_L4WD_STAT_WDT_STAT register field. */
#define ALT_L4WD_STAT_WDT_STAT_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L4WD_STAT_WDT_STAT register field. */
#define ALT_L4WD_STAT_WDT_STAT_MSB        0
/* The width in bits of the ALT_L4WD_STAT_WDT_STAT register field. */
#define ALT_L4WD_STAT_WDT_STAT_WIDTH      1
/* The mask used to set the ALT_L4WD_STAT_WDT_STAT register field value. */
#define ALT_L4WD_STAT_WDT_STAT_SET_MSK    0x00000001
/* The mask used to clear the ALT_L4WD_STAT_WDT_STAT register field value. */
#define ALT_L4WD_STAT_WDT_STAT_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L4WD_STAT_WDT_STAT register field. */
#define ALT_L4WD_STAT_WDT_STAT_RESET      0x0
/* Extracts the ALT_L4WD_STAT_WDT_STAT field value from a register. */
#define ALT_L4WD_STAT_WDT_STAT_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L4WD_STAT_WDT_STAT register field value suitable for setting the register. */
#define ALT_L4WD_STAT_WDT_STAT_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L4WD_STAT.
 */
struct ALT_L4WD_STAT_s
{
    const uint32_t  wdt_stat :  1;  /* Interrupt Status */
    uint32_t                 : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L4WD_STAT. */
typedef volatile struct ALT_L4WD_STAT_s  ALT_L4WD_STAT_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L4WD_STAT register from the beginning of the component. */
#define ALT_L4WD_STAT_OFST        0x10
/* The address of the ALT_L4WD_STAT register. */
#define ALT_L4WD_STAT_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L4WD_STAT_OFST))

/*
 * Register : Interrupt Clear Register - wdt_eoi
 * 
 * Clears the watchdog interrupt when read.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description    
 * :-------|:-------|:------|:----------------
 *  [0]    | R      | 0x0   | Interrupt Clear
 *  [31:1] | ???    | 0x0   | *UNDEFINED*    
 * 
 */
/*
 * Field : Interrupt Clear - wdt_eoi
 * 
 * Clears the watchdog interrupt. This can be used to clear the interrupt without
 * restarting the watchdog counter.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_L4WD_EOI_WDT_EOI register field. */
#define ALT_L4WD_EOI_WDT_EOI_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L4WD_EOI_WDT_EOI register field. */
#define ALT_L4WD_EOI_WDT_EOI_MSB        0
/* The width in bits of the ALT_L4WD_EOI_WDT_EOI register field. */
#define ALT_L4WD_EOI_WDT_EOI_WIDTH      1
/* The mask used to set the ALT_L4WD_EOI_WDT_EOI register field value. */
#define ALT_L4WD_EOI_WDT_EOI_SET_MSK    0x00000001
/* The mask used to clear the ALT_L4WD_EOI_WDT_EOI register field value. */
#define ALT_L4WD_EOI_WDT_EOI_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L4WD_EOI_WDT_EOI register field. */
#define ALT_L4WD_EOI_WDT_EOI_RESET      0x0
/* Extracts the ALT_L4WD_EOI_WDT_EOI field value from a register. */
#define ALT_L4WD_EOI_WDT_EOI_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L4WD_EOI_WDT_EOI register field value suitable for setting the register. */
#define ALT_L4WD_EOI_WDT_EOI_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L4WD_EOI.
 */
struct ALT_L4WD_EOI_s
{
    const uint32_t  wdt_eoi :  1;  /* Interrupt Clear */
    uint32_t                : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L4WD_EOI. */
typedef volatile struct ALT_L4WD_EOI_s  ALT_L4WD_EOI_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L4WD_EOI register from the beginning of the component. */
#define ALT_L4WD_EOI_OFST        0x14
/* The address of the ALT_L4WD_EOI register. */
#define ALT_L4WD_EOI_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L4WD_EOI_OFST))

/*
 * Register : Component Parameters Register 5 - cp_wdt_user_top_max
 * 
 * This is a constant read-only register that contains encoded information about
 * the component's parameter settings.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description           
 * :-------|:-------|:------|:-----------------------
 *  [31:0] | R      | 0x0   | Component Parameters 5
 * 
 */
/*
 * Field : Component Parameters 5 - cp_wdt_user_top_max
 * 
 * Upper limit of Timeout Period parameters.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL register field. */
#define ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL register field. */
#define ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL_MSB        31
/* The width in bits of the ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL register field. */
#define ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL_WIDTH      32
/* The mask used to set the ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL register field value. */
#define ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL_SET_MSK    0xffffffff
/* The mask used to clear the ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL register field value. */
#define ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL_CLR_MSK    0x00000000
/* The reset value of the ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL register field. */
#define ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL_RESET      0x0
/* Extracts the ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL field value from a register. */
#define ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL register field value suitable for setting the register. */
#define ALT_L4WD_CP_WDT_USER_TOP_MAX_VAL_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L4WD_CP_WDT_USER_TOP_MAX.
 */
struct ALT_L4WD_CP_WDT_USER_TOP_MAX_s
{
    const uint32_t  cp_wdt_user_top_max : 32;  /* Component Parameters 5 */
};

/* The typedef declaration for register ALT_L4WD_CP_WDT_USER_TOP_MAX. */
typedef volatile struct ALT_L4WD_CP_WDT_USER_TOP_MAX_s  ALT_L4WD_CP_WDT_USER_TOP_MAX_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L4WD_CP_WDT_USER_TOP_MAX register from the beginning of the component. */
#define ALT_L4WD_CP_WDT_USER_TOP_MAX_OFST        0xe4
/* The address of the ALT_L4WD_CP_WDT_USER_TOP_MAX register. */
#define ALT_L4WD_CP_WDT_USER_TOP_MAX_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L4WD_CP_WDT_USER_TOP_MAX_OFST))

/*
 * Register : Component Parameters Register 4 - cp_wdt_user_top_init_max
 * 
 * This is a constant read-only register that contains encoded information about
 * the component's parameter settings
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description           
 * :-------|:-------|:------|:-----------------------
 *  [31:0] | R      | 0x0   | Component Parameters 4
 * 
 */
/*
 * Field : Component Parameters 4 - cp_wdt_user_top_init_max
 * 
 * Upper limit of Initial Timeout Period parameters.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL register field. */
#define ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL register field. */
#define ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL_MSB        31
/* The width in bits of the ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL register field. */
#define ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL_WIDTH      32
/* The mask used to set the ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL register field value. */
#define ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL_SET_MSK    0xffffffff
/* The mask used to clear the ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL register field value. */
#define ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL_CLR_MSK    0x00000000
/* The reset value of the ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL register field. */
#define ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL_RESET      0x0
/* Extracts the ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL field value from a register. */
#define ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL register field value suitable for setting the register. */
#define ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_VAL_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX.
 */
struct ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_s
{
    const uint32_t  cp_wdt_user_top_init_max : 32;  /* Component Parameters 4 */
};

/* The typedef declaration for register ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX. */
typedef volatile struct ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_s  ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX register from the beginning of the component. */
#define ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_OFST        0xe8
/* The address of the ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX register. */
#define ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_OFST))

/*
 * Register : Component Parameters Register 3 - cd_wdt_top_rst
 * 
 * This is a constant read-only register that contains encoded information about
 * the component's parameter settings.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description            
 * :-------|:-------|:------|:------------------------
 *  [31:0] | R      | 0xff  | Component Parameters  3
 * 
 */
/*
 * Field : Component Parameters  3 - cd_wdt_top_rst
 * 
 * Contains the reset value of the WDT_TORR register.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST register field. */
#define ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST register field. */
#define ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST_MSB        31
/* The width in bits of the ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST register field. */
#define ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST_WIDTH      32
/* The mask used to set the ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST register field value. */
#define ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST_SET_MSK    0xffffffff
/* The mask used to clear the ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST register field value. */
#define ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST_CLR_MSK    0x00000000
/* The reset value of the ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST register field. */
#define ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST_RESET      0xff
/* Extracts the ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST field value from a register. */
#define ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST register field value suitable for setting the register. */
#define ALT_L4WD_CD_WDT_TOP_RST_CD_WDT_TOP_RST_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L4WD_CD_WDT_TOP_RST.
 */
struct ALT_L4WD_CD_WDT_TOP_RST_s
{
    const uint32_t  cd_wdt_top_rst : 32;  /* Component Parameters  3 */
};

/* The typedef declaration for register ALT_L4WD_CD_WDT_TOP_RST. */
typedef volatile struct ALT_L4WD_CD_WDT_TOP_RST_s  ALT_L4WD_CD_WDT_TOP_RST_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L4WD_CD_WDT_TOP_RST register from the beginning of the component. */
#define ALT_L4WD_CD_WDT_TOP_RST_OFST        0xec
/* The address of the ALT_L4WD_CD_WDT_TOP_RST register. */
#define ALT_L4WD_CD_WDT_TOP_RST_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L4WD_CD_WDT_TOP_RST_OFST))

/*
 * Register : Component Parameters  Register 2 - cp_wdt_cnt_rst
 * 
 * This is a constant read-only register that contains encoded information about
 * the component's parameter settings.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset      | Description            
 * :-------|:-------|:-----------|:------------------------
 *  [31:0] | R      | 0x7fffffff | Component Parameters  2
 * 
 */
/*
 * Field : Component Parameters  2 - cp_wdt_cnt_rst
 * 
 * The timeout period range is fixed. The range increments by the power of 2 from 2
 * to the 16 to 2 to the 31.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST register field. */
#define ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST register field. */
#define ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST_MSB        31
/* The width in bits of the ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST register field. */
#define ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST_WIDTH      32
/* The mask used to set the ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST register field value. */
#define ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST_SET_MSK    0xffffffff
/* The mask used to clear the ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST register field value. */
#define ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST_CLR_MSK    0x00000000
/* The reset value of the ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST register field. */
#define ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST_RESET      0x7fffffff
/* Extracts the ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST field value from a register. */
#define ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST register field value suitable for setting the register. */
#define ALT_L4WD_CP_WDT_CNT_RST_CP_WDT_CNT_RST_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L4WD_CP_WDT_CNT_RST.
 */
struct ALT_L4WD_CP_WDT_CNT_RST_s
{
    const uint32_t  cp_wdt_cnt_rst : 32;  /* Component Parameters  2 */
};

/* The typedef declaration for register ALT_L4WD_CP_WDT_CNT_RST. */
typedef volatile struct ALT_L4WD_CP_WDT_CNT_RST_s  ALT_L4WD_CP_WDT_CNT_RST_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L4WD_CP_WDT_CNT_RST register from the beginning of the component. */
#define ALT_L4WD_CP_WDT_CNT_RST_OFST        0xf0
/* The address of the ALT_L4WD_CP_WDT_CNT_RST register. */
#define ALT_L4WD_CP_WDT_CNT_RST_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L4WD_CP_WDT_CNT_RST_OFST))

/*
 * Register : Component Parameters Register 1 - wdt_comp_param_1
 * 
 * This is a constant read-only register that contains encoded information about
 * the component's parameter settings.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                           
 * :--------|:-------|:------|:---------------------------------------
 *  [0]     | R      | 0x0   | Always Enable                         
 *  [1]     | R      | 0x0   | Default Mode                          
 *  [2]     | R      | 0x1   | Dual Timeout Period                   
 *  [3]     | R      | 0x0   | Hardcode Response Mode                
 *  [4]     | R      | 0x1   | Hardcode Reset Pulse Length           
 *  [5]     | R      | 0x0   | Hardcode Timeout Period               
 *  [6]     | R      | 0x1   | Use Pre-defined (Fixed) Timeout Values
 *  [7]     | R      | 0x0   | Include Pause Input                   
 *  [9:8]   | R      | 0x2   | APB Data Width                        
 *  [12:10] | R      | 0x0   | Default Reset Pulse Length            
 *  [15:13] | ???    | 0x0   | *UNDEFINED*                           
 *  [19:16] | R      | 0xf   | Default Timeout Period                
 *  [23:20] | R      | 0xf   | Default Initial Timeout Period        
 *  [28:24] | R      | 0x10  | Counter Width in Bits                 
 *  [31:29] | ???    | 0x0   | *UNDEFINED*                           
 * 
 */
/*
 * Field : Always Enable - cp_wdt_always_en
 * 
 * Specifies whether watchdog starts after reset or not.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                          | Value | Description               
 * :----------------------------------------------|:------|:---------------------------
 *  ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN_E_DISD | 0x0   | Watchdog disabled on reset
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN
 * 
 * Watchdog disabled on reset
 */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN_E_DISD   0x0

/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN_MSB        0
/* The width in bits of the ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN_WIDTH      1
/* The mask used to set the ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN_SET_MSK    0x00000001
/* The mask used to clear the ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN_RESET      0x0
/* Extracts the ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN field value from a register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN register field value suitable for setting the register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_ALWAYS_EN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Default Mode - cp_wdt_dflt_rmod
 * 
 * Specifies default output response mode after reset.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                            | Value | Description                                     
 * :------------------------------------------------|:------|:-------------------------------------------------
 *  ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD_E_RSTREQ | 0x0   | Generate a warm reset request (don't generate an
 * :                                                |       | interrupt first)                                
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD
 * 
 * Generate a warm reset request (don't generate an interrupt first)
 */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD_E_RSTREQ 0x0

/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD_MSB        1
/* The width in bits of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD_WIDTH      1
/* The mask used to set the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD_SET_MSK    0x00000002
/* The mask used to clear the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD_CLR_MSK    0xfffffffd
/* The reset value of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD_RESET      0x0
/* Extracts the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD field value from a register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD register field value suitable for setting the register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RMOD_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Dual Timeout Period - cp_wdt_dual_top
 * 
 * Specifies whether a second timeout period that is used for initialization prior
 * to the first kick is present or not.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                            | Value | Description                     
 * :------------------------------------------------|:------|:---------------------------------
 *  ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP_E_DUALTOP | 0x1   | Second timeout period is present
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP
 * 
 * Second timeout period is present
 */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP_E_DUALTOP 0x1

/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP_MSB        2
/* The width in bits of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP_WIDTH      1
/* The mask used to set the ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP_SET_MSK    0x00000004
/* The mask used to clear the ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP_CLR_MSK    0xfffffffb
/* The reset value of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP_RESET      0x1
/* Extracts the ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP field value from a register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP register field value suitable for setting the register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DUAL_TOP_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Hardcode Response Mode - cp_wdt_hc_rmod
 * 
 * Specifies if response mode (when counter reaches 0) is programmable or
 * hardcoded.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                        | Value | Description                          
 * :--------------------------------------------|:------|:--------------------------------------
 *  ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD_E_PGML | 0x0   | Output response mode is programmable.
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD
 * 
 * Output response mode is programmable.
 */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD_E_PGML 0x0

/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD_MSB        3
/* The width in bits of the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD_WIDTH      1
/* The mask used to set the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD_SET_MSK    0x00000008
/* The mask used to clear the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD_CLR_MSK    0xfffffff7
/* The reset value of the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD_RESET      0x0
/* Extracts the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD field value from a register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD register field value suitable for setting the register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RMOD_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : Hardcode Reset Pulse Length - cp_wdt_hc_rpl
 * 
 * Specifies if the reset pulse length is programmable or hardcoded.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                            | Value | Description                     
 * :------------------------------------------------|:------|:---------------------------------
 *  ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL_E_HARDCODED | 0x1   | Reset pulse length is hardcoded.
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL
 * 
 * Reset pulse length is hardcoded.
 */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL_E_HARDCODED 0x1

/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL_MSB        4
/* The width in bits of the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL_WIDTH      1
/* The mask used to set the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL_SET_MSK    0x00000010
/* The mask used to clear the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL_CLR_MSK    0xffffffef
/* The reset value of the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL_RESET      0x1
/* Extracts the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL field value from a register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL register field value suitable for setting the register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_RPL_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : Hardcode Timeout Period - cp_wdt_hc_top
 * 
 * Specifies if the timeout period is programmable or hardcoded.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                       | Value | Description                    
 * :-------------------------------------------|:------|:--------------------------------
 *  ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP_E_PGML | 0x0   | Timeout period is programmable.
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP
 * 
 * Timeout period is programmable.
 */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP_E_PGML  0x0

/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP_MSB        5
/* The width in bits of the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP_WIDTH      1
/* The mask used to set the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP_SET_MSK    0x00000020
/* The mask used to clear the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP_CLR_MSK    0xffffffdf
/* The reset value of the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP_RESET      0x0
/* Extracts the ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP field value from a register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP register field value suitable for setting the register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_HC_TOP_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : Use Pre-defined (Fixed) Timeout Values - cp_wdt_use_fix_top
 * 
 * Specifies if the watchdog uses the pre-defined timeout values or if these were
 * overriden with customer values when the watchdog was configured.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                  | Value | Description                                  
 * :------------------------------------------------------|:------|:----------------------------------------------
 *  ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP_E_PREDEFINED | 0x1   | Use pre-defined (fixed) timeout values (range
 * :                                                      |       | from 2**16 to 2**31)                         
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP
 * 
 * Use pre-defined (fixed) timeout values (range from 2**16 to 2**31)
 */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP_E_PREDEFINED   0x1

/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP_MSB        6
/* The width in bits of the ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP_WIDTH      1
/* The mask used to set the ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP_SET_MSK    0x00000040
/* The mask used to clear the ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP_CLR_MSK    0xffffffbf
/* The reset value of the ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP_RESET      0x1
/* Extracts the ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP field value from a register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP register field value suitable for setting the register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_USE_FIX_TOP_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : Include Pause Input - cp_wdt_pause
 * 
 * Should specify if the pause input is included or not. However, this field is
 * always hardwired to 0 so you can't figure this out by reading this field. The
 * pause input is included and can be used to pause the watchdog when the MPU is in
 * debug mode.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE_MSB        7
/* The width in bits of the ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE_WIDTH      1
/* The mask used to set the ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE_SET_MSK    0x00000080
/* The mask used to clear the ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE_CLR_MSK    0xffffff7f
/* The reset value of the ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE_RESET      0x0
/* Extracts the ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE field value from a register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE register field value suitable for setting the register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_PAUSE_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : APB Data Width - cp_wdt_apb_data_width
 * 
 * APB Bus Width
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                      | Value | Description              
 * :----------------------------------------------------------|:------|:--------------------------
 *  ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH_E_WIDTH32BITS | 0x2   | APB Data Width is 32 Bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH
 * 
 * APB Data Width is 32 Bits
 */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH_E_WIDTH32BITS   0x2

/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH_MSB        9
/* The width in bits of the ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH_WIDTH      2
/* The mask used to set the ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH_SET_MSK    0x00000300
/* The mask used to clear the ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH_CLR_MSK    0xfffffcff
/* The reset value of the ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH_RESET      0x2
/* Extracts the ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH field value from a register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH_GET(value) (((value) & 0x00000300) >> 8)
/* Produces a ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH register field value suitable for setting the register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_APB_DATA_WIDTH_SET(value) (((value) << 8) & 0x00000300)

/*
 * Field : Default Reset Pulse Length - cp_wdt_dflt_rpl
 * 
 * Specifies the reset pulse length in cycles.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                 | Value | Description                    
 * :-----------------------------------------------------|:------|:--------------------------------
 *  ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL_E_PULSE2CYCLES | 0x0   | Reset pulse length of 2 cycles.
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL
 * 
 * Reset pulse length of 2 cycles.
 */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL_E_PULSE2CYCLES    0x0

/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL_MSB        12
/* The width in bits of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL_WIDTH      3
/* The mask used to set the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL_SET_MSK    0x00001c00
/* The mask used to clear the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL_CLR_MSK    0xffffe3ff
/* The reset value of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL_RESET      0x0
/* Extracts the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL field value from a register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL_GET(value) (((value) & 0x00001c00) >> 10)
/* Produces a ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL register field value suitable for setting the register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_RPL_SET(value) (((value) << 10) & 0x00001c00)

/*
 * Field : Default Timeout Period - cp_wdt_dflt_top
 * 
 * Specifies the timeout period that is available directly after reset.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                          | Value | Description                         
 * :----------------------------------------------|:------|:-------------------------------------
 *  ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_E_TMO15 | 0xf   | Timeout period is 15 (2**31 cycles).
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP
 * 
 * Timeout period is 15 (2**31 cycles).
 */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_E_TMO15   0xf

/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_LSB        16
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_MSB        19
/* The width in bits of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_WIDTH      4
/* The mask used to set the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_SET_MSK    0x000f0000
/* The mask used to clear the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_CLR_MSK    0xfff0ffff
/* The reset value of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_RESET      0xf
/* Extracts the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP field value from a register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_GET(value) (((value) & 0x000f0000) >> 16)
/* Produces a ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP register field value suitable for setting the register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_SET(value) (((value) << 16) & 0x000f0000)

/*
 * Field : Default Initial Timeout Period - cp_wdt_dflt_top_init
 * 
 * Specifies the initial timeout period that is available directly after reset.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                               | Value | Description                                 
 * :---------------------------------------------------|:------|:---------------------------------------------
 *  ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT_E_TMO15 | 0xf   | Initial timeout period is 15 (2**31 cycles).
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT
 * 
 * Initial timeout period is 15 (2**31 cycles).
 */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT_E_TMO15  0xf

/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT_LSB        20
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT_MSB        23
/* The width in bits of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT_WIDTH      4
/* The mask used to set the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT_SET_MSK    0x00f00000
/* The mask used to clear the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT_CLR_MSK    0xff0fffff
/* The reset value of the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT_RESET      0xf
/* Extracts the ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT field value from a register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT_GET(value) (((value) & 0x00f00000) >> 20)
/* Produces a ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT register field value suitable for setting the register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_DFLT_TOP_INIT_SET(value) (((value) << 20) & 0x00f00000)

/*
 * Field : Counter Width in Bits - cp_wdt_cnt_width
 * 
 * Width of counter in bits less 16.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                                 | Value | Description             
 * :-----------------------------------------------------|:------|:-------------------------
 *  ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH_E_WIDTH32BITS | 0x10  | Counter width is 32 bits
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH
 * 
 * Counter width is 32 bits
 */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH_E_WIDTH32BITS    0x10

/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH_LSB        24
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH_MSB        28
/* The width in bits of the ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH_WIDTH      5
/* The mask used to set the ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH_SET_MSK    0x1f000000
/* The mask used to clear the ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH register field value. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH_CLR_MSK    0xe0ffffff
/* The reset value of the ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH register field. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH_RESET      0x10
/* Extracts the ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH field value from a register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH_GET(value) (((value) & 0x1f000000) >> 24)
/* Produces a ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH register field value suitable for setting the register. */
#define ALT_L4WD_COMP_PARAM_1_CP_WDT_CNT_WIDTH_SET(value) (((value) << 24) & 0x1f000000)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L4WD_COMP_PARAM_1.
 */
struct ALT_L4WD_COMP_PARAM_1_s
{
    const uint32_t  cp_wdt_always_en      :  1;  /* Always Enable */
    const uint32_t  cp_wdt_dflt_rmod      :  1;  /* Default Mode */
    const uint32_t  cp_wdt_dual_top       :  1;  /* Dual Timeout Period */
    const uint32_t  cp_wdt_hc_rmod        :  1;  /* Hardcode Response Mode */
    const uint32_t  cp_wdt_hc_rpl         :  1;  /* Hardcode Reset Pulse Length */
    const uint32_t  cp_wdt_hc_top         :  1;  /* Hardcode Timeout Period */
    const uint32_t  cp_wdt_use_fix_top    :  1;  /* Use Pre-defined (Fixed) Timeout Values */
    const uint32_t  cp_wdt_pause          :  1;  /* Include Pause Input */
    const uint32_t  cp_wdt_apb_data_width :  2;  /* APB Data Width */
    const uint32_t  cp_wdt_dflt_rpl       :  3;  /* Default Reset Pulse Length */
    uint32_t                              :  3;  /* *UNDEFINED* */
    const uint32_t  cp_wdt_dflt_top       :  4;  /* Default Timeout Period */
    const uint32_t  cp_wdt_dflt_top_init  :  4;  /* Default Initial Timeout Period */
    const uint32_t  cp_wdt_cnt_width      :  5;  /* Counter Width in Bits */
    uint32_t                              :  3;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L4WD_COMP_PARAM_1. */
typedef volatile struct ALT_L4WD_COMP_PARAM_1_s  ALT_L4WD_COMP_PARAM_1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L4WD_COMP_PARAM_1 register from the beginning of the component. */
#define ALT_L4WD_COMP_PARAM_1_OFST        0xf4
/* The address of the ALT_L4WD_COMP_PARAM_1 register. */
#define ALT_L4WD_COMP_PARAM_1_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L4WD_COMP_PARAM_1_OFST))

/*
 * Register : Component Version Register - wdt_comp_version
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset      | Description      
 * :-------|:-------|:-----------|:------------------
 *  [31:0] | R      | 0x3130362a | Component Version
 * 
 */
/*
 * Field : Component Version - wdt_comp_version
 * 
 * ASCII value for each number in the version, followed by *. For example,
 * 32_30_31_2A represents the version 2.01*.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_VER_WDT_COMP_VER register field. */
#define ALT_L4WD_COMP_VER_WDT_COMP_VER_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_VER_WDT_COMP_VER register field. */
#define ALT_L4WD_COMP_VER_WDT_COMP_VER_MSB        31
/* The width in bits of the ALT_L4WD_COMP_VER_WDT_COMP_VER register field. */
#define ALT_L4WD_COMP_VER_WDT_COMP_VER_WIDTH      32
/* The mask used to set the ALT_L4WD_COMP_VER_WDT_COMP_VER register field value. */
#define ALT_L4WD_COMP_VER_WDT_COMP_VER_SET_MSK    0xffffffff
/* The mask used to clear the ALT_L4WD_COMP_VER_WDT_COMP_VER register field value. */
#define ALT_L4WD_COMP_VER_WDT_COMP_VER_CLR_MSK    0x00000000
/* The reset value of the ALT_L4WD_COMP_VER_WDT_COMP_VER register field. */
#define ALT_L4WD_COMP_VER_WDT_COMP_VER_RESET      0x3130362a
/* Extracts the ALT_L4WD_COMP_VER_WDT_COMP_VER field value from a register. */
#define ALT_L4WD_COMP_VER_WDT_COMP_VER_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_L4WD_COMP_VER_WDT_COMP_VER register field value suitable for setting the register. */
#define ALT_L4WD_COMP_VER_WDT_COMP_VER_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L4WD_COMP_VER.
 */
struct ALT_L4WD_COMP_VER_s
{
    const uint32_t  wdt_comp_version : 32;  /* Component Version */
};

/* The typedef declaration for register ALT_L4WD_COMP_VER. */
typedef volatile struct ALT_L4WD_COMP_VER_s  ALT_L4WD_COMP_VER_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L4WD_COMP_VER register from the beginning of the component. */
#define ALT_L4WD_COMP_VER_OFST        0xf8
/* The address of the ALT_L4WD_COMP_VER register. */
#define ALT_L4WD_COMP_VER_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L4WD_COMP_VER_OFST))

/*
 * Register : Component Type Register - wdt_comp_type
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset      | Description   
 * :-------|:-------|:-----------|:---------------
 *  [31:0] | R      | 0x44570120 | Component Type
 * 
 */
/*
 * Field : Component Type - wdt_comp_type
 * 
 * Designware Component Type number = 0x44_57_01_20.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE register field. */
#define ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE register field. */
#define ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE_MSB        31
/* The width in bits of the ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE register field. */
#define ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE_WIDTH      32
/* The mask used to set the ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE register field value. */
#define ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE_SET_MSK    0xffffffff
/* The mask used to clear the ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE register field value. */
#define ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE_CLR_MSK    0x00000000
/* The reset value of the ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE register field. */
#define ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE_RESET      0x44570120
/* Extracts the ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE field value from a register. */
#define ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE_GET(value) (((value) & 0xffffffff) >> 0)
/* Produces a ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE register field value suitable for setting the register. */
#define ALT_L4WD_COMP_TYPE_WDT_COMP_TYPE_SET(value) (((value) << 0) & 0xffffffff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L4WD_COMP_TYPE.
 */
struct ALT_L4WD_COMP_TYPE_s
{
    const uint32_t  wdt_comp_type : 32;  /* Component Type */
};

/* The typedef declaration for register ALT_L4WD_COMP_TYPE. */
typedef volatile struct ALT_L4WD_COMP_TYPE_s  ALT_L4WD_COMP_TYPE_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L4WD_COMP_TYPE register from the beginning of the component. */
#define ALT_L4WD_COMP_TYPE_OFST        0xfc
/* The address of the ALT_L4WD_COMP_TYPE register. */
#define ALT_L4WD_COMP_TYPE_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L4WD_COMP_TYPE_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_L4WD.
 */
struct ALT_L4WD_s
{
    volatile ALT_L4WD_CR_t                        wdt_cr;                    /* ALT_L4WD_CR */
    volatile ALT_L4WD_TORR_t                      wdt_torr;                  /* ALT_L4WD_TORR */
    volatile ALT_L4WD_CCVR_t                      wdt_ccvr;                  /* ALT_L4WD_CCVR */
    volatile ALT_L4WD_CRR_t                       wdt_crr;                   /* ALT_L4WD_CRR */
    volatile ALT_L4WD_STAT_t                      wdt_stat;                  /* ALT_L4WD_STAT */
    volatile ALT_L4WD_EOI_t                       wdt_eoi;                   /* ALT_L4WD_EOI */
    volatile uint32_t                             _pad_0x18_0xe3[51];        /* *UNDEFINED* */
    volatile ALT_L4WD_CP_WDT_USER_TOP_MAX_t       cp_wdt_user_top_max;       /* ALT_L4WD_CP_WDT_USER_TOP_MAX */
    volatile ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX_t  cp_wdt_user_top_init_max;  /* ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX */
    volatile ALT_L4WD_CD_WDT_TOP_RST_t            cd_wdt_top_rst;            /* ALT_L4WD_CD_WDT_TOP_RST */
    volatile ALT_L4WD_CP_WDT_CNT_RST_t            cp_wdt_cnt_rst;            /* ALT_L4WD_CP_WDT_CNT_RST */
    volatile ALT_L4WD_COMP_PARAM_1_t              wdt_comp_param_1;          /* ALT_L4WD_COMP_PARAM_1 */
    volatile ALT_L4WD_COMP_VER_t                  wdt_comp_version;          /* ALT_L4WD_COMP_VER */
    volatile ALT_L4WD_COMP_TYPE_t                 wdt_comp_type;             /* ALT_L4WD_COMP_TYPE */
};

/* The typedef declaration for register group ALT_L4WD. */
typedef volatile struct ALT_L4WD_s  ALT_L4WD_t;
/* The struct declaration for the raw register contents of register group ALT_L4WD. */
struct ALT_L4WD_raw_s
{
    volatile uint32_t  wdt_cr;                    /* ALT_L4WD_CR */
    volatile uint32_t  wdt_torr;                  /* ALT_L4WD_TORR */
    volatile uint32_t  wdt_ccvr;                  /* ALT_L4WD_CCVR */
    volatile uint32_t  wdt_crr;                   /* ALT_L4WD_CRR */
    volatile uint32_t  wdt_stat;                  /* ALT_L4WD_STAT */
    volatile uint32_t  wdt_eoi;                   /* ALT_L4WD_EOI */
    volatile uint32_t  _pad_0x18_0xe3[51];        /* *UNDEFINED* */
    volatile uint32_t  cp_wdt_user_top_max;       /* ALT_L4WD_CP_WDT_USER_TOP_MAX */
    volatile uint32_t  cp_wdt_user_top_init_max;  /* ALT_L4WD_CP_WDT_USER_TOP_INIT_MAX */
    volatile uint32_t  cd_wdt_top_rst;            /* ALT_L4WD_CD_WDT_TOP_RST */
    volatile uint32_t  cp_wdt_cnt_rst;            /* ALT_L4WD_CP_WDT_CNT_RST */
    volatile uint32_t  wdt_comp_param_1;          /* ALT_L4WD_COMP_PARAM_1 */
    volatile uint32_t  wdt_comp_version;          /* ALT_L4WD_COMP_VER */
    volatile uint32_t  wdt_comp_type;             /* ALT_L4WD_COMP_TYPE */
};

/* The typedef declaration for the raw register contents of register group ALT_L4WD. */
typedef volatile struct ALT_L4WD_raw_s  ALT_L4WD_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_L4WD_H__ */

