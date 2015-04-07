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

/* Altera - ALT_L3 */

#ifndef __ALTERA_ALT_L3_H__
#define __ALTERA_ALT_L3_H__

#ifdef __cplusplus
extern "C"
{
#endif  /* __cplusplus */

/*
 * Component : L3 (NIC-301) GPV Registers - ALT_L3
 * L3 (NIC-301) GPV Registers
 * 
 * Registers to control L3 interconnect settings
 * 
 */
/*
 * Register : Remap - remap
 * 
 * The L3 interconnect has separate address maps for the various L3 Masters.
 * Generally, the addresses are the same for most masters. However, the sparse
 * interconnect of the L3 switch causes some masters to have holes in their memory
 * maps. The remap bits are not mutually exclusive. Each bit can be set
 * independently and in combinations. Priority for the bits is determined by the
 * bit offset: lower offset bits take precedence over higher offset bits.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                     
 * :-------|:-------|:------|:---------------------------------
 *  [0]    | W      | 0x0   | MPU at 0x0                      
 *  [1]    | W      | 0x0   | Non-MPU at 0x0                  
 *  [2]    | ???    | 0x0   | *UNDEFINED*                     
 *  [3]    | W      | 0x0   | HPS2FPGA AXI Bridge Visibility  
 *  [4]    | W      | 0x0   | LWHPS2FPGA AXI Bridge Visibility
 *  [31:5] | ???    | 0x0   | *UNDEFINED*                     
 * 
 */
/*
 * Field : MPU at 0x0 - mpuzero
 * 
 * Controls whether address 0x0 for the MPU L3 master is mapped to the Boot ROM or
 * On-chip RAM.  This field only has an effect on the MPU L3 master.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description                                     
 * :-------------------------------|:------|:-------------------------------------------------
 *  ALT_L3_REMAP_MPUZERO_E_BOOTROM | 0x0   | Maps the Boot ROM to address 0x0 for the MPU L3 
 * :                               |       | master. Note that the Boot ROM is also always   
 * :                               |       | mapped to address 0xfffd_0000 for the MPU L3    
 * :                               |       | master independent of this field's value.       
 *  ALT_L3_REMAP_MPUZERO_E_OCRAM   | 0x1   | Maps the On-chip RAM to address 0x0 for the MPU 
 * :                               |       | L3 master. Note that the On-chip RAM is also    
 * :                               |       | always mapped to address 0xffff_0000 for the MPU
 * :                               |       | L3 master independent of this field's value.    
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_REMAP_MPUZERO
 * 
 * Maps the Boot ROM to address 0x0 for the MPU L3 master. Note that the Boot ROM
 * is also always mapped to address 0xfffd_0000 for the MPU L3 master independent
 * of this field's value.
 */
#define ALT_L3_REMAP_MPUZERO_E_BOOTROM  0x0
/*
 * Enumerated value for register field ALT_L3_REMAP_MPUZERO
 * 
 * Maps the On-chip RAM to address 0x0 for the MPU L3 master. Note that the On-chip
 * RAM is also always mapped to address 0xffff_0000 for the MPU L3 master
 * independent of this field's value.
 */
#define ALT_L3_REMAP_MPUZERO_E_OCRAM    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_REMAP_MPUZERO register field. */
#define ALT_L3_REMAP_MPUZERO_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_REMAP_MPUZERO register field. */
#define ALT_L3_REMAP_MPUZERO_MSB        0
/* The width in bits of the ALT_L3_REMAP_MPUZERO register field. */
#define ALT_L3_REMAP_MPUZERO_WIDTH      1
/* The mask used to set the ALT_L3_REMAP_MPUZERO register field value. */
#define ALT_L3_REMAP_MPUZERO_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_REMAP_MPUZERO register field value. */
#define ALT_L3_REMAP_MPUZERO_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_REMAP_MPUZERO register field. */
#define ALT_L3_REMAP_MPUZERO_RESET      0x0
/* Extracts the ALT_L3_REMAP_MPUZERO field value from a register. */
#define ALT_L3_REMAP_MPUZERO_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_REMAP_MPUZERO register field value suitable for setting the register. */
#define ALT_L3_REMAP_MPUZERO_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Non-MPU at 0x0 - nonmpuzero
 * 
 * Controls whether address 0x0 for the non-MPU L3 masters is mapped to the SDRAM
 * or On-chip RAM.  This field only has an effect on the non-MPU L3 masters. The
 * non-MPU L3 masters are the DMA controllers (standalone and those built-in to
 * peripherals), the FPGA2HPS AXI Bridge, and the DAP.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description                                     
 * :--------------------------------|:------|:-------------------------------------------------
 *  ALT_L3_REMAP_NONMPUZERO_E_SDRAM | 0x0   | Maps the SDRAM to address 0x0 for the non-MPU L3
 * :                                |       | masters.                                        
 *  ALT_L3_REMAP_NONMPUZERO_E_OCRAM | 0x1   | Maps the On-chip RAM to address 0x0 for the non-
 * :                                |       | MPU L3 masters. Note that the On-chip RAM is    
 * :                                |       | also always mapped to address 0xffff_0000 for   
 * :                                |       | the non-MPU L3 masters independent of this      
 * :                                |       | field's value.                                  
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_REMAP_NONMPUZERO
 * 
 * Maps the SDRAM to address 0x0 for the non-MPU L3 masters.
 */
#define ALT_L3_REMAP_NONMPUZERO_E_SDRAM 0x0
/*
 * Enumerated value for register field ALT_L3_REMAP_NONMPUZERO
 * 
 * Maps the On-chip RAM to address 0x0 for the non-MPU L3 masters. Note that the
 * On-chip RAM is also always mapped to address 0xffff_0000 for the non-MPU L3
 * masters independent of this field's value.
 */
#define ALT_L3_REMAP_NONMPUZERO_E_OCRAM 0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_REMAP_NONMPUZERO register field. */
#define ALT_L3_REMAP_NONMPUZERO_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_L3_REMAP_NONMPUZERO register field. */
#define ALT_L3_REMAP_NONMPUZERO_MSB        1
/* The width in bits of the ALT_L3_REMAP_NONMPUZERO register field. */
#define ALT_L3_REMAP_NONMPUZERO_WIDTH      1
/* The mask used to set the ALT_L3_REMAP_NONMPUZERO register field value. */
#define ALT_L3_REMAP_NONMPUZERO_SET_MSK    0x00000002
/* The mask used to clear the ALT_L3_REMAP_NONMPUZERO register field value. */
#define ALT_L3_REMAP_NONMPUZERO_CLR_MSK    0xfffffffd
/* The reset value of the ALT_L3_REMAP_NONMPUZERO register field. */
#define ALT_L3_REMAP_NONMPUZERO_RESET      0x0
/* Extracts the ALT_L3_REMAP_NONMPUZERO field value from a register. */
#define ALT_L3_REMAP_NONMPUZERO_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_L3_REMAP_NONMPUZERO register field value suitable for setting the register. */
#define ALT_L3_REMAP_NONMPUZERO_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : HPS2FPGA AXI Bridge Visibility - hps2fpga
 * 
 * Controls whether the HPS2FPGA AXI Bridge is visible to L3 masters or not.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description                                    
 * :-----------------------------|:------|:------------------------------------------------
 *  ALT_L3_REMAP_H2F_E_INVISIBLE | 0x0   | The HPS2FPGA AXI Bridge is not visible to L3   
 * :                             |       | masters. Accesses to the associated address    
 * :                             |       | range return an AXI decode error to the master.
 *  ALT_L3_REMAP_H2F_E_VISIBLE   | 0x1   | The HPS2FPGA AXI Bridge is visible to L3       
 * :                             |       | masters.                                       
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_REMAP_H2F
 * 
 * The HPS2FPGA AXI Bridge is not visible to L3 masters. Accesses to the associated
 * address range return an AXI decode error to the master.
 */
#define ALT_L3_REMAP_H2F_E_INVISIBLE    0x0
/*
 * Enumerated value for register field ALT_L3_REMAP_H2F
 * 
 * The HPS2FPGA AXI Bridge is visible to L3 masters.
 */
#define ALT_L3_REMAP_H2F_E_VISIBLE      0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_REMAP_H2F register field. */
#define ALT_L3_REMAP_H2F_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_L3_REMAP_H2F register field. */
#define ALT_L3_REMAP_H2F_MSB        3
/* The width in bits of the ALT_L3_REMAP_H2F register field. */
#define ALT_L3_REMAP_H2F_WIDTH      1
/* The mask used to set the ALT_L3_REMAP_H2F register field value. */
#define ALT_L3_REMAP_H2F_SET_MSK    0x00000008
/* The mask used to clear the ALT_L3_REMAP_H2F register field value. */
#define ALT_L3_REMAP_H2F_CLR_MSK    0xfffffff7
/* The reset value of the ALT_L3_REMAP_H2F register field. */
#define ALT_L3_REMAP_H2F_RESET      0x0
/* Extracts the ALT_L3_REMAP_H2F field value from a register. */
#define ALT_L3_REMAP_H2F_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_L3_REMAP_H2F register field value suitable for setting the register. */
#define ALT_L3_REMAP_H2F_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : LWHPS2FPGA AXI Bridge Visibility - lwhps2fpga
 * 
 * Controls whether the Lightweight HPS2FPGA AXI Bridge is visible to L3 masters or
 * not.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description                                    
 * :-------------------------------|:------|:------------------------------------------------
 *  ALT_L3_REMAP_LWH2F_E_INVISIBLE | 0x0   | The LWHPS2FPGA AXI Bridge is not visible to L3 
 * :                               |       | masters. Accesses to the associated address    
 * :                               |       | range return an AXI decode error to the master.
 *  ALT_L3_REMAP_LWH2F_E_VISIBLE   | 0x1   | The LWHPS2FPGA AXI Bridge is visible to L3     
 * :                               |       | masters.                                       
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_REMAP_LWH2F
 * 
 * The LWHPS2FPGA AXI Bridge is not visible to L3 masters. Accesses to the
 * associated address range return an AXI decode error to the master.
 */
#define ALT_L3_REMAP_LWH2F_E_INVISIBLE  0x0
/*
 * Enumerated value for register field ALT_L3_REMAP_LWH2F
 * 
 * The LWHPS2FPGA AXI Bridge is visible to L3 masters.
 */
#define ALT_L3_REMAP_LWH2F_E_VISIBLE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_REMAP_LWH2F register field. */
#define ALT_L3_REMAP_LWH2F_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_L3_REMAP_LWH2F register field. */
#define ALT_L3_REMAP_LWH2F_MSB        4
/* The width in bits of the ALT_L3_REMAP_LWH2F register field. */
#define ALT_L3_REMAP_LWH2F_WIDTH      1
/* The mask used to set the ALT_L3_REMAP_LWH2F register field value. */
#define ALT_L3_REMAP_LWH2F_SET_MSK    0x00000010
/* The mask used to clear the ALT_L3_REMAP_LWH2F register field value. */
#define ALT_L3_REMAP_LWH2F_CLR_MSK    0xffffffef
/* The reset value of the ALT_L3_REMAP_LWH2F register field. */
#define ALT_L3_REMAP_LWH2F_RESET      0x0
/* Extracts the ALT_L3_REMAP_LWH2F field value from a register. */
#define ALT_L3_REMAP_LWH2F_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_L3_REMAP_LWH2F register field value suitable for setting the register. */
#define ALT_L3_REMAP_LWH2F_SET(value) (((value) << 4) & 0x00000010)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_REMAP.
 */
struct ALT_L3_REMAP_s
{
    uint32_t  mpuzero    :  1;  /* MPU at 0x0 */
    uint32_t  nonmpuzero :  1;  /* Non-MPU at 0x0 */
    uint32_t             :  1;  /* *UNDEFINED* */
    uint32_t  hps2fpga   :  1;  /* HPS2FPGA AXI Bridge Visibility */
    uint32_t  lwhps2fpga :  1;  /* LWHPS2FPGA AXI Bridge Visibility */
    uint32_t             : 27;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_REMAP. */
typedef volatile struct ALT_L3_REMAP_s  ALT_L3_REMAP_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_REMAP register from the beginning of the component. */
#define ALT_L3_REMAP_OFST        0x0

/*
 * Register Group : Security Register Group - ALT_L3_SECGRP
 * Security Register Group
 * 
 * Registers that control slave security.
 * 
 */
/*
 * Register : L4 Main Peripherals Security - l4main
 * 
 * Controls security settings for L4 Main peripherals.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description            
 * :-------|:-------|:------|:------------------------
 *  [0]    | W      | 0x0   | SPI Slave 0 Security   
 *  [1]    | W      | 0x0   | SPI Slave 1 Security   
 *  [2]    | W      | 0x0   | DMA Secure Security    
 *  [3]    | W      | 0x0   | DMA Non-secure Security
 *  [31:4] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : SPI Slave 0 Security - spis0
 * 
 * Controls whether secure or non-secure masters can access the SPI Slave 0 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                                  
 * :------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4MAIN_SPIS0_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                    |       | master.                                      
 *  ALT_L3_SEC_L4MAIN_SPIS0_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                    |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4MAIN_SPIS0
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4MAIN_SPIS0_E_SECURE    0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4MAIN_SPIS0
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4MAIN_SPIS0_E_NONSECURE 0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4MAIN_SPIS0 register field. */
#define ALT_L3_SEC_L4MAIN_SPIS0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4MAIN_SPIS0 register field. */
#define ALT_L3_SEC_L4MAIN_SPIS0_MSB        0
/* The width in bits of the ALT_L3_SEC_L4MAIN_SPIS0 register field. */
#define ALT_L3_SEC_L4MAIN_SPIS0_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4MAIN_SPIS0 register field value. */
#define ALT_L3_SEC_L4MAIN_SPIS0_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_L4MAIN_SPIS0 register field value. */
#define ALT_L3_SEC_L4MAIN_SPIS0_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_L4MAIN_SPIS0 register field. */
#define ALT_L3_SEC_L4MAIN_SPIS0_RESET      0x0
/* Extracts the ALT_L3_SEC_L4MAIN_SPIS0 field value from a register. */
#define ALT_L3_SEC_L4MAIN_SPIS0_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_L4MAIN_SPIS0 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4MAIN_SPIS0_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : SPI Slave 1 Security - spis1
 * 
 * Controls whether secure or non-secure masters can access the SPI Slave 1 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                                  
 * :------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4MAIN_SPIS1_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                    |       | master.                                      
 *  ALT_L3_SEC_L4MAIN_SPIS1_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                    |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4MAIN_SPIS1
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4MAIN_SPIS1_E_SECURE    0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4MAIN_SPIS1
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4MAIN_SPIS1_E_NONSECURE 0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4MAIN_SPIS1 register field. */
#define ALT_L3_SEC_L4MAIN_SPIS1_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4MAIN_SPIS1 register field. */
#define ALT_L3_SEC_L4MAIN_SPIS1_MSB        1
/* The width in bits of the ALT_L3_SEC_L4MAIN_SPIS1 register field. */
#define ALT_L3_SEC_L4MAIN_SPIS1_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4MAIN_SPIS1 register field value. */
#define ALT_L3_SEC_L4MAIN_SPIS1_SET_MSK    0x00000002
/* The mask used to clear the ALT_L3_SEC_L4MAIN_SPIS1 register field value. */
#define ALT_L3_SEC_L4MAIN_SPIS1_CLR_MSK    0xfffffffd
/* The reset value of the ALT_L3_SEC_L4MAIN_SPIS1 register field. */
#define ALT_L3_SEC_L4MAIN_SPIS1_RESET      0x0
/* Extracts the ALT_L3_SEC_L4MAIN_SPIS1 field value from a register. */
#define ALT_L3_SEC_L4MAIN_SPIS1_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_L3_SEC_L4MAIN_SPIS1 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4MAIN_SPIS1_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : DMA Secure Security - dmasecure
 * 
 * Controls whether secure or non-secure masters can access the DMA Secure slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                    | Value | Description                                  
 * :----------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4MAIN_DMASECURE_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                        |       | master.                                      
 *  ALT_L3_SEC_L4MAIN_DMASECURE_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                        |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4MAIN_DMASECURE
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4MAIN_DMASECURE_E_SECURE    0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4MAIN_DMASECURE
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4MAIN_DMASECURE_E_NONSECURE 0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4MAIN_DMASECURE register field. */
#define ALT_L3_SEC_L4MAIN_DMASECURE_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4MAIN_DMASECURE register field. */
#define ALT_L3_SEC_L4MAIN_DMASECURE_MSB        2
/* The width in bits of the ALT_L3_SEC_L4MAIN_DMASECURE register field. */
#define ALT_L3_SEC_L4MAIN_DMASECURE_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4MAIN_DMASECURE register field value. */
#define ALT_L3_SEC_L4MAIN_DMASECURE_SET_MSK    0x00000004
/* The mask used to clear the ALT_L3_SEC_L4MAIN_DMASECURE register field value. */
#define ALT_L3_SEC_L4MAIN_DMASECURE_CLR_MSK    0xfffffffb
/* The reset value of the ALT_L3_SEC_L4MAIN_DMASECURE register field. */
#define ALT_L3_SEC_L4MAIN_DMASECURE_RESET      0x0
/* Extracts the ALT_L3_SEC_L4MAIN_DMASECURE field value from a register. */
#define ALT_L3_SEC_L4MAIN_DMASECURE_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_L3_SEC_L4MAIN_DMASECURE register field value suitable for setting the register. */
#define ALT_L3_SEC_L4MAIN_DMASECURE_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : DMA Non-secure Security - dmanonsecure
 * 
 * Controls whether secure or non-secure masters can access the DMA Non-secure
 * slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                       | Value | Description                                  
 * :-------------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4MAIN_DMANONSECURE_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                           |       | master.                                      
 *  ALT_L3_SEC_L4MAIN_DMANONSECURE_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                           |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4MAIN_DMANONSECURE
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4MAIN_DMANONSECURE_E_SECURE     0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4MAIN_DMANONSECURE
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4MAIN_DMANONSECURE_E_NONSECURE  0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4MAIN_DMANONSECURE register field. */
#define ALT_L3_SEC_L4MAIN_DMANONSECURE_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4MAIN_DMANONSECURE register field. */
#define ALT_L3_SEC_L4MAIN_DMANONSECURE_MSB        3
/* The width in bits of the ALT_L3_SEC_L4MAIN_DMANONSECURE register field. */
#define ALT_L3_SEC_L4MAIN_DMANONSECURE_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4MAIN_DMANONSECURE register field value. */
#define ALT_L3_SEC_L4MAIN_DMANONSECURE_SET_MSK    0x00000008
/* The mask used to clear the ALT_L3_SEC_L4MAIN_DMANONSECURE register field value. */
#define ALT_L3_SEC_L4MAIN_DMANONSECURE_CLR_MSK    0xfffffff7
/* The reset value of the ALT_L3_SEC_L4MAIN_DMANONSECURE register field. */
#define ALT_L3_SEC_L4MAIN_DMANONSECURE_RESET      0x0
/* Extracts the ALT_L3_SEC_L4MAIN_DMANONSECURE field value from a register. */
#define ALT_L3_SEC_L4MAIN_DMANONSECURE_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_L3_SEC_L4MAIN_DMANONSECURE register field value suitable for setting the register. */
#define ALT_L3_SEC_L4MAIN_DMANONSECURE_SET(value) (((value) << 3) & 0x00000008)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_L4MAIN.
 */
struct ALT_L3_SEC_L4MAIN_s
{
    uint32_t  spis0        :  1;  /* SPI Slave 0 Security */
    uint32_t  spis1        :  1;  /* SPI Slave 1 Security */
    uint32_t  dmasecure    :  1;  /* DMA Secure Security */
    uint32_t  dmanonsecure :  1;  /* DMA Non-secure Security */
    uint32_t               : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_L4MAIN. */
typedef volatile struct ALT_L3_SEC_L4MAIN_s  ALT_L3_SEC_L4MAIN_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_L4MAIN register from the beginning of the component. */
#define ALT_L3_SEC_L4MAIN_OFST        0x0

/*
 * Register : L4 SP Peripherals Security - l4sp
 * 
 * Controls security settings for L4 SP peripherals.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description             
 * :--------|:-------|:------|:-------------------------
 *  [0]     | W      | 0x0   | SDRAM Registers Security
 *  [1]     | W      | 0x0   | SP Timer 0 Security     
 *  [2]     | W      | 0x0   | I2C0 Security           
 *  [3]     | W      | 0x0   | I2C1 Security           
 *  [4]     | W      | 0x0   | I2C2 (EMAC 0) Security  
 *  [5]     | W      | 0x0   | I2C3 (EMAC 1) Security  
 *  [6]     | W      | 0x0   | UART 0 Security         
 *  [7]     | W      | 0x0   | UART 1 Security         
 *  [8]     | W      | 0x0   | CAN 0 Security          
 *  [9]     | W      | 0x0   | CAN 1 Security          
 *  [10]    | W      | 0x0   | SP Timer 1 Security     
 *  [31:11] | ???    | 0x0   | *UNDEFINED*             
 * 
 */
/*
 * Field : SDRAM Registers Security - sdrregs
 * 
 * Controls whether secure or non-secure masters can access the SDRAM Registers
 * slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                                  
 * :------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4SP_SDRREGS_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                    |       | master.                                      
 *  ALT_L3_SEC_L4SP_SDRREGS_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                    |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_SDRREGS
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4SP_SDRREGS_E_SECURE    0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_SDRREGS
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4SP_SDRREGS_E_NONSECURE 0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4SP_SDRREGS register field. */
#define ALT_L3_SEC_L4SP_SDRREGS_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4SP_SDRREGS register field. */
#define ALT_L3_SEC_L4SP_SDRREGS_MSB        0
/* The width in bits of the ALT_L3_SEC_L4SP_SDRREGS register field. */
#define ALT_L3_SEC_L4SP_SDRREGS_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4SP_SDRREGS register field value. */
#define ALT_L3_SEC_L4SP_SDRREGS_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_L4SP_SDRREGS register field value. */
#define ALT_L3_SEC_L4SP_SDRREGS_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_L4SP_SDRREGS register field. */
#define ALT_L3_SEC_L4SP_SDRREGS_RESET      0x0
/* Extracts the ALT_L3_SEC_L4SP_SDRREGS field value from a register. */
#define ALT_L3_SEC_L4SP_SDRREGS_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_L4SP_SDRREGS register field value suitable for setting the register. */
#define ALT_L3_SEC_L4SP_SDRREGS_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : SP Timer 0 Security - sptimer0
 * 
 * Controls whether secure or non-secure masters can access the SP Timer 0 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                                  
 * :-----------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4SP_SPTMR0_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                   |       | master.                                      
 *  ALT_L3_SEC_L4SP_SPTMR0_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                   |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_SPTMR0
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4SP_SPTMR0_E_SECURE     0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_SPTMR0
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4SP_SPTMR0_E_NONSECURE  0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4SP_SPTMR0 register field. */
#define ALT_L3_SEC_L4SP_SPTMR0_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4SP_SPTMR0 register field. */
#define ALT_L3_SEC_L4SP_SPTMR0_MSB        1
/* The width in bits of the ALT_L3_SEC_L4SP_SPTMR0 register field. */
#define ALT_L3_SEC_L4SP_SPTMR0_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4SP_SPTMR0 register field value. */
#define ALT_L3_SEC_L4SP_SPTMR0_SET_MSK    0x00000002
/* The mask used to clear the ALT_L3_SEC_L4SP_SPTMR0 register field value. */
#define ALT_L3_SEC_L4SP_SPTMR0_CLR_MSK    0xfffffffd
/* The reset value of the ALT_L3_SEC_L4SP_SPTMR0 register field. */
#define ALT_L3_SEC_L4SP_SPTMR0_RESET      0x0
/* Extracts the ALT_L3_SEC_L4SP_SPTMR0 field value from a register. */
#define ALT_L3_SEC_L4SP_SPTMR0_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_L3_SEC_L4SP_SPTMR0 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4SP_SPTMR0_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : I2C0 Security - i2c0
 * 
 * Controls whether secure or non-secure masters can access the I2C0 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                                  
 * :---------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4SP_I2C0_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                 |       | master.                                      
 *  ALT_L3_SEC_L4SP_I2C0_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                 |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_I2C0
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4SP_I2C0_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_I2C0
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4SP_I2C0_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4SP_I2C0 register field. */
#define ALT_L3_SEC_L4SP_I2C0_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4SP_I2C0 register field. */
#define ALT_L3_SEC_L4SP_I2C0_MSB        2
/* The width in bits of the ALT_L3_SEC_L4SP_I2C0 register field. */
#define ALT_L3_SEC_L4SP_I2C0_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4SP_I2C0 register field value. */
#define ALT_L3_SEC_L4SP_I2C0_SET_MSK    0x00000004
/* The mask used to clear the ALT_L3_SEC_L4SP_I2C0 register field value. */
#define ALT_L3_SEC_L4SP_I2C0_CLR_MSK    0xfffffffb
/* The reset value of the ALT_L3_SEC_L4SP_I2C0 register field. */
#define ALT_L3_SEC_L4SP_I2C0_RESET      0x0
/* Extracts the ALT_L3_SEC_L4SP_I2C0 field value from a register. */
#define ALT_L3_SEC_L4SP_I2C0_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_L3_SEC_L4SP_I2C0 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4SP_I2C0_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : I2C1 Security - i2c1
 * 
 * Controls whether secure or non-secure masters can access the I2C1 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                                  
 * :---------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4SP_I2C1_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                 |       | master.                                      
 *  ALT_L3_SEC_L4SP_I2C1_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                 |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_I2C1
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4SP_I2C1_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_I2C1
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4SP_I2C1_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4SP_I2C1 register field. */
#define ALT_L3_SEC_L4SP_I2C1_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4SP_I2C1 register field. */
#define ALT_L3_SEC_L4SP_I2C1_MSB        3
/* The width in bits of the ALT_L3_SEC_L4SP_I2C1 register field. */
#define ALT_L3_SEC_L4SP_I2C1_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4SP_I2C1 register field value. */
#define ALT_L3_SEC_L4SP_I2C1_SET_MSK    0x00000008
/* The mask used to clear the ALT_L3_SEC_L4SP_I2C1 register field value. */
#define ALT_L3_SEC_L4SP_I2C1_CLR_MSK    0xfffffff7
/* The reset value of the ALT_L3_SEC_L4SP_I2C1 register field. */
#define ALT_L3_SEC_L4SP_I2C1_RESET      0x0
/* Extracts the ALT_L3_SEC_L4SP_I2C1 field value from a register. */
#define ALT_L3_SEC_L4SP_I2C1_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_L3_SEC_L4SP_I2C1 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4SP_I2C1_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : I2C2 (EMAC 0) Security - i2c2
 * 
 * Controls whether secure or non-secure masters can access the I2C2 (EMAC 0)
 * slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                                  
 * :---------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4SP_I2C2_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                 |       | master.                                      
 *  ALT_L3_SEC_L4SP_I2C2_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                 |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_I2C2
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4SP_I2C2_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_I2C2
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4SP_I2C2_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4SP_I2C2 register field. */
#define ALT_L3_SEC_L4SP_I2C2_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4SP_I2C2 register field. */
#define ALT_L3_SEC_L4SP_I2C2_MSB        4
/* The width in bits of the ALT_L3_SEC_L4SP_I2C2 register field. */
#define ALT_L3_SEC_L4SP_I2C2_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4SP_I2C2 register field value. */
#define ALT_L3_SEC_L4SP_I2C2_SET_MSK    0x00000010
/* The mask used to clear the ALT_L3_SEC_L4SP_I2C2 register field value. */
#define ALT_L3_SEC_L4SP_I2C2_CLR_MSK    0xffffffef
/* The reset value of the ALT_L3_SEC_L4SP_I2C2 register field. */
#define ALT_L3_SEC_L4SP_I2C2_RESET      0x0
/* Extracts the ALT_L3_SEC_L4SP_I2C2 field value from a register. */
#define ALT_L3_SEC_L4SP_I2C2_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_L3_SEC_L4SP_I2C2 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4SP_I2C2_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : I2C3 (EMAC 1) Security - i2c3
 * 
 * Controls whether secure or non-secure masters can access the I2C3 (EMAC 1)
 * slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                                  
 * :---------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4SP_I2C3_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                 |       | master.                                      
 *  ALT_L3_SEC_L4SP_I2C3_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                 |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_I2C3
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4SP_I2C3_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_I2C3
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4SP_I2C3_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4SP_I2C3 register field. */
#define ALT_L3_SEC_L4SP_I2C3_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4SP_I2C3 register field. */
#define ALT_L3_SEC_L4SP_I2C3_MSB        5
/* The width in bits of the ALT_L3_SEC_L4SP_I2C3 register field. */
#define ALT_L3_SEC_L4SP_I2C3_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4SP_I2C3 register field value. */
#define ALT_L3_SEC_L4SP_I2C3_SET_MSK    0x00000020
/* The mask used to clear the ALT_L3_SEC_L4SP_I2C3 register field value. */
#define ALT_L3_SEC_L4SP_I2C3_CLR_MSK    0xffffffdf
/* The reset value of the ALT_L3_SEC_L4SP_I2C3 register field. */
#define ALT_L3_SEC_L4SP_I2C3_RESET      0x0
/* Extracts the ALT_L3_SEC_L4SP_I2C3 field value from a register. */
#define ALT_L3_SEC_L4SP_I2C3_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_L3_SEC_L4SP_I2C3 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4SP_I2C3_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : UART 0 Security - uart0
 * 
 * Controls whether secure or non-secure masters can access the UART 0 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                  
 * :----------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4SP_UART0_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                  |       | master.                                      
 *  ALT_L3_SEC_L4SP_UART0_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                  |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_UART0
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4SP_UART0_E_SECURE      0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_UART0
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4SP_UART0_E_NONSECURE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4SP_UART0 register field. */
#define ALT_L3_SEC_L4SP_UART0_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4SP_UART0 register field. */
#define ALT_L3_SEC_L4SP_UART0_MSB        6
/* The width in bits of the ALT_L3_SEC_L4SP_UART0 register field. */
#define ALT_L3_SEC_L4SP_UART0_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4SP_UART0 register field value. */
#define ALT_L3_SEC_L4SP_UART0_SET_MSK    0x00000040
/* The mask used to clear the ALT_L3_SEC_L4SP_UART0 register field value. */
#define ALT_L3_SEC_L4SP_UART0_CLR_MSK    0xffffffbf
/* The reset value of the ALT_L3_SEC_L4SP_UART0 register field. */
#define ALT_L3_SEC_L4SP_UART0_RESET      0x0
/* Extracts the ALT_L3_SEC_L4SP_UART0 field value from a register. */
#define ALT_L3_SEC_L4SP_UART0_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_L3_SEC_L4SP_UART0 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4SP_UART0_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : UART 1 Security - uart1
 * 
 * Controls whether secure or non-secure masters can access the UART 1 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                  
 * :----------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4SP_UART1_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                  |       | master.                                      
 *  ALT_L3_SEC_L4SP_UART1_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                  |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_UART1
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4SP_UART1_E_SECURE      0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_UART1
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4SP_UART1_E_NONSECURE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4SP_UART1 register field. */
#define ALT_L3_SEC_L4SP_UART1_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4SP_UART1 register field. */
#define ALT_L3_SEC_L4SP_UART1_MSB        7
/* The width in bits of the ALT_L3_SEC_L4SP_UART1 register field. */
#define ALT_L3_SEC_L4SP_UART1_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4SP_UART1 register field value. */
#define ALT_L3_SEC_L4SP_UART1_SET_MSK    0x00000080
/* The mask used to clear the ALT_L3_SEC_L4SP_UART1 register field value. */
#define ALT_L3_SEC_L4SP_UART1_CLR_MSK    0xffffff7f
/* The reset value of the ALT_L3_SEC_L4SP_UART1 register field. */
#define ALT_L3_SEC_L4SP_UART1_RESET      0x0
/* Extracts the ALT_L3_SEC_L4SP_UART1 field value from a register. */
#define ALT_L3_SEC_L4SP_UART1_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_L3_SEC_L4SP_UART1 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4SP_UART1_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : CAN 0 Security - can0
 * 
 * Controls whether secure or non-secure masters can access the CAN 0 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                                  
 * :---------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4SP_CAN0_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                 |       | master.                                      
 *  ALT_L3_SEC_L4SP_CAN0_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                 |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_CAN0
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4SP_CAN0_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_CAN0
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4SP_CAN0_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4SP_CAN0 register field. */
#define ALT_L3_SEC_L4SP_CAN0_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4SP_CAN0 register field. */
#define ALT_L3_SEC_L4SP_CAN0_MSB        8
/* The width in bits of the ALT_L3_SEC_L4SP_CAN0 register field. */
#define ALT_L3_SEC_L4SP_CAN0_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4SP_CAN0 register field value. */
#define ALT_L3_SEC_L4SP_CAN0_SET_MSK    0x00000100
/* The mask used to clear the ALT_L3_SEC_L4SP_CAN0 register field value. */
#define ALT_L3_SEC_L4SP_CAN0_CLR_MSK    0xfffffeff
/* The reset value of the ALT_L3_SEC_L4SP_CAN0 register field. */
#define ALT_L3_SEC_L4SP_CAN0_RESET      0x0
/* Extracts the ALT_L3_SEC_L4SP_CAN0 field value from a register. */
#define ALT_L3_SEC_L4SP_CAN0_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_L3_SEC_L4SP_CAN0 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4SP_CAN0_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : CAN 1 Security - can1
 * 
 * Controls whether secure or non-secure masters can access the CAN 1 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                                  
 * :---------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4SP_CAN1_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                 |       | master.                                      
 *  ALT_L3_SEC_L4SP_CAN1_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                 |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_CAN1
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4SP_CAN1_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_CAN1
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4SP_CAN1_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4SP_CAN1 register field. */
#define ALT_L3_SEC_L4SP_CAN1_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4SP_CAN1 register field. */
#define ALT_L3_SEC_L4SP_CAN1_MSB        9
/* The width in bits of the ALT_L3_SEC_L4SP_CAN1 register field. */
#define ALT_L3_SEC_L4SP_CAN1_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4SP_CAN1 register field value. */
#define ALT_L3_SEC_L4SP_CAN1_SET_MSK    0x00000200
/* The mask used to clear the ALT_L3_SEC_L4SP_CAN1 register field value. */
#define ALT_L3_SEC_L4SP_CAN1_CLR_MSK    0xfffffdff
/* The reset value of the ALT_L3_SEC_L4SP_CAN1 register field. */
#define ALT_L3_SEC_L4SP_CAN1_RESET      0x0
/* Extracts the ALT_L3_SEC_L4SP_CAN1 field value from a register. */
#define ALT_L3_SEC_L4SP_CAN1_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_L3_SEC_L4SP_CAN1 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4SP_CAN1_SET(value) (((value) << 9) & 0x00000200)

/*
 * Field : SP Timer 1 Security - sptimer1
 * 
 * Controls whether secure or non-secure masters can access the SP Timer 1 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                               | Value | Description                                  
 * :-----------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4SP_SPTMR1_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                   |       | master.                                      
 *  ALT_L3_SEC_L4SP_SPTMR1_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                   |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_SPTMR1
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4SP_SPTMR1_E_SECURE     0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4SP_SPTMR1
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4SP_SPTMR1_E_NONSECURE  0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4SP_SPTMR1 register field. */
#define ALT_L3_SEC_L4SP_SPTMR1_LSB        10
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4SP_SPTMR1 register field. */
#define ALT_L3_SEC_L4SP_SPTMR1_MSB        10
/* The width in bits of the ALT_L3_SEC_L4SP_SPTMR1 register field. */
#define ALT_L3_SEC_L4SP_SPTMR1_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4SP_SPTMR1 register field value. */
#define ALT_L3_SEC_L4SP_SPTMR1_SET_MSK    0x00000400
/* The mask used to clear the ALT_L3_SEC_L4SP_SPTMR1 register field value. */
#define ALT_L3_SEC_L4SP_SPTMR1_CLR_MSK    0xfffffbff
/* The reset value of the ALT_L3_SEC_L4SP_SPTMR1 register field. */
#define ALT_L3_SEC_L4SP_SPTMR1_RESET      0x0
/* Extracts the ALT_L3_SEC_L4SP_SPTMR1 field value from a register. */
#define ALT_L3_SEC_L4SP_SPTMR1_GET(value) (((value) & 0x00000400) >> 10)
/* Produces a ALT_L3_SEC_L4SP_SPTMR1 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4SP_SPTMR1_SET(value) (((value) << 10) & 0x00000400)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_L4SP.
 */
struct ALT_L3_SEC_L4SP_s
{
    uint32_t  sdrregs  :  1;  /* SDRAM Registers Security */
    uint32_t  sptimer0 :  1;  /* SP Timer 0 Security */
    uint32_t  i2c0     :  1;  /* I2C0 Security */
    uint32_t  i2c1     :  1;  /* I2C1 Security */
    uint32_t  i2c2     :  1;  /* I2C2 (EMAC 0) Security */
    uint32_t  i2c3     :  1;  /* I2C3 (EMAC 1) Security */
    uint32_t  uart0    :  1;  /* UART 0 Security */
    uint32_t  uart1    :  1;  /* UART 1 Security */
    uint32_t  can0     :  1;  /* CAN 0 Security */
    uint32_t  can1     :  1;  /* CAN 1 Security */
    uint32_t  sptimer1 :  1;  /* SP Timer 1 Security */
    uint32_t           : 21;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_L4SP. */
typedef volatile struct ALT_L3_SEC_L4SP_s  ALT_L3_SEC_L4SP_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_L4SP register from the beginning of the component. */
#define ALT_L3_SEC_L4SP_OFST        0x4

/*
 * Register : L4 MP Peripherals Security - l4mp
 * 
 * Controls security settings for L4 MP peripherals.
 * 
 * Register Layout
 * 
 *  Bits    | Access | Reset | Description                   
 * :--------|:-------|:------|:-------------------------------
 *  [0]     | W      | 0x0   | FPGA Manager Register Security
 *  [1]     | W      | 0x0   | DAP Security                  
 *  [2]     | W      | 0x0   | QSPI Registers Security       
 *  [3]     | W      | 0x0   | SDMMC Security                
 *  [4]     | W      | 0x0   | EMAC 0 Security               
 *  [5]     | W      | 0x0   | EMAC 1 Security               
 *  [6]     | W      | 0x0   | ACP ID Mapper Security        
 *  [7]     | W      | 0x0   | GPIO 0 Security               
 *  [8]     | W      | 0x0   | GPIO 1 Security               
 *  [9]     | W      | 0x0   | GPIO 2 Security               
 *  [31:10] | ???    | 0x0   | *UNDEFINED*                   
 * 
 */
/*
 * Field : FPGA Manager Register Security - fpgamgrregs
 * 
 * Controls whether secure or non-secure masters can access the FPGA Manager
 * Register slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                                  
 * :------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4MP_FPGAMGR_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                    |       | master.                                      
 *  ALT_L3_SEC_L4MP_FPGAMGR_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                    |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_FPGAMGR
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4MP_FPGAMGR_E_SECURE    0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_FPGAMGR
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4MP_FPGAMGR_E_NONSECURE 0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4MP_FPGAMGR register field. */
#define ALT_L3_SEC_L4MP_FPGAMGR_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4MP_FPGAMGR register field. */
#define ALT_L3_SEC_L4MP_FPGAMGR_MSB        0
/* The width in bits of the ALT_L3_SEC_L4MP_FPGAMGR register field. */
#define ALT_L3_SEC_L4MP_FPGAMGR_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4MP_FPGAMGR register field value. */
#define ALT_L3_SEC_L4MP_FPGAMGR_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_L4MP_FPGAMGR register field value. */
#define ALT_L3_SEC_L4MP_FPGAMGR_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_L4MP_FPGAMGR register field. */
#define ALT_L3_SEC_L4MP_FPGAMGR_RESET      0x0
/* Extracts the ALT_L3_SEC_L4MP_FPGAMGR field value from a register. */
#define ALT_L3_SEC_L4MP_FPGAMGR_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_L4MP_FPGAMGR register field value suitable for setting the register. */
#define ALT_L3_SEC_L4MP_FPGAMGR_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : DAP Security - dap
 * 
 * Controls whether secure or non-secure masters can access the DAP slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description                                  
 * :--------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4MP_DAP_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                |       | master.                                      
 *  ALT_L3_SEC_L4MP_DAP_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_DAP
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4MP_DAP_E_SECURE    0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_DAP
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4MP_DAP_E_NONSECURE 0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4MP_DAP register field. */
#define ALT_L3_SEC_L4MP_DAP_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4MP_DAP register field. */
#define ALT_L3_SEC_L4MP_DAP_MSB        1
/* The width in bits of the ALT_L3_SEC_L4MP_DAP register field. */
#define ALT_L3_SEC_L4MP_DAP_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4MP_DAP register field value. */
#define ALT_L3_SEC_L4MP_DAP_SET_MSK    0x00000002
/* The mask used to clear the ALT_L3_SEC_L4MP_DAP register field value. */
#define ALT_L3_SEC_L4MP_DAP_CLR_MSK    0xfffffffd
/* The reset value of the ALT_L3_SEC_L4MP_DAP register field. */
#define ALT_L3_SEC_L4MP_DAP_RESET      0x0
/* Extracts the ALT_L3_SEC_L4MP_DAP field value from a register. */
#define ALT_L3_SEC_L4MP_DAP_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_L3_SEC_L4MP_DAP register field value suitable for setting the register. */
#define ALT_L3_SEC_L4MP_DAP_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : QSPI Registers Security - qspiregs
 * 
 * Controls whether secure or non-secure masters can access the QSPI Registers
 * slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                                  
 * :---------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4MP_QSPI_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                 |       | master.                                      
 *  ALT_L3_SEC_L4MP_QSPI_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                 |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_QSPI
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4MP_QSPI_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_QSPI
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4MP_QSPI_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4MP_QSPI register field. */
#define ALT_L3_SEC_L4MP_QSPI_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4MP_QSPI register field. */
#define ALT_L3_SEC_L4MP_QSPI_MSB        2
/* The width in bits of the ALT_L3_SEC_L4MP_QSPI register field. */
#define ALT_L3_SEC_L4MP_QSPI_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4MP_QSPI register field value. */
#define ALT_L3_SEC_L4MP_QSPI_SET_MSK    0x00000004
/* The mask used to clear the ALT_L3_SEC_L4MP_QSPI register field value. */
#define ALT_L3_SEC_L4MP_QSPI_CLR_MSK    0xfffffffb
/* The reset value of the ALT_L3_SEC_L4MP_QSPI register field. */
#define ALT_L3_SEC_L4MP_QSPI_RESET      0x0
/* Extracts the ALT_L3_SEC_L4MP_QSPI field value from a register. */
#define ALT_L3_SEC_L4MP_QSPI_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_L3_SEC_L4MP_QSPI register field value suitable for setting the register. */
#define ALT_L3_SEC_L4MP_QSPI_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : SDMMC Security - sdmmc
 * 
 * Controls whether secure or non-secure masters can access the SDMMC slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                  
 * :----------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4MP_SDMMC_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                  |       | master.                                      
 *  ALT_L3_SEC_L4MP_SDMMC_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                  |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_SDMMC
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4MP_SDMMC_E_SECURE      0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_SDMMC
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4MP_SDMMC_E_NONSECURE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4MP_SDMMC register field. */
#define ALT_L3_SEC_L4MP_SDMMC_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4MP_SDMMC register field. */
#define ALT_L3_SEC_L4MP_SDMMC_MSB        3
/* The width in bits of the ALT_L3_SEC_L4MP_SDMMC register field. */
#define ALT_L3_SEC_L4MP_SDMMC_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4MP_SDMMC register field value. */
#define ALT_L3_SEC_L4MP_SDMMC_SET_MSK    0x00000008
/* The mask used to clear the ALT_L3_SEC_L4MP_SDMMC register field value. */
#define ALT_L3_SEC_L4MP_SDMMC_CLR_MSK    0xfffffff7
/* The reset value of the ALT_L3_SEC_L4MP_SDMMC register field. */
#define ALT_L3_SEC_L4MP_SDMMC_RESET      0x0
/* Extracts the ALT_L3_SEC_L4MP_SDMMC field value from a register. */
#define ALT_L3_SEC_L4MP_SDMMC_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_L3_SEC_L4MP_SDMMC register field value suitable for setting the register. */
#define ALT_L3_SEC_L4MP_SDMMC_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : EMAC 0 Security - emac0
 * 
 * Controls whether secure or non-secure masters can access the EMAC 0 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                  
 * :----------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4MP_EMAC0_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                  |       | master.                                      
 *  ALT_L3_SEC_L4MP_EMAC0_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                  |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_EMAC0
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4MP_EMAC0_E_SECURE      0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_EMAC0
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4MP_EMAC0_E_NONSECURE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4MP_EMAC0 register field. */
#define ALT_L3_SEC_L4MP_EMAC0_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4MP_EMAC0 register field. */
#define ALT_L3_SEC_L4MP_EMAC0_MSB        4
/* The width in bits of the ALT_L3_SEC_L4MP_EMAC0 register field. */
#define ALT_L3_SEC_L4MP_EMAC0_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4MP_EMAC0 register field value. */
#define ALT_L3_SEC_L4MP_EMAC0_SET_MSK    0x00000010
/* The mask used to clear the ALT_L3_SEC_L4MP_EMAC0 register field value. */
#define ALT_L3_SEC_L4MP_EMAC0_CLR_MSK    0xffffffef
/* The reset value of the ALT_L3_SEC_L4MP_EMAC0 register field. */
#define ALT_L3_SEC_L4MP_EMAC0_RESET      0x0
/* Extracts the ALT_L3_SEC_L4MP_EMAC0 field value from a register. */
#define ALT_L3_SEC_L4MP_EMAC0_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_L3_SEC_L4MP_EMAC0 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4MP_EMAC0_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : EMAC 1 Security - emac1
 * 
 * Controls whether secure or non-secure masters can access the EMAC 1 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                  
 * :----------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4MP_EMAC1_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                  |       | master.                                      
 *  ALT_L3_SEC_L4MP_EMAC1_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                  |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_EMAC1
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4MP_EMAC1_E_SECURE      0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_EMAC1
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4MP_EMAC1_E_NONSECURE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4MP_EMAC1 register field. */
#define ALT_L3_SEC_L4MP_EMAC1_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4MP_EMAC1 register field. */
#define ALT_L3_SEC_L4MP_EMAC1_MSB        5
/* The width in bits of the ALT_L3_SEC_L4MP_EMAC1 register field. */
#define ALT_L3_SEC_L4MP_EMAC1_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4MP_EMAC1 register field value. */
#define ALT_L3_SEC_L4MP_EMAC1_SET_MSK    0x00000020
/* The mask used to clear the ALT_L3_SEC_L4MP_EMAC1 register field value. */
#define ALT_L3_SEC_L4MP_EMAC1_CLR_MSK    0xffffffdf
/* The reset value of the ALT_L3_SEC_L4MP_EMAC1 register field. */
#define ALT_L3_SEC_L4MP_EMAC1_RESET      0x0
/* Extracts the ALT_L3_SEC_L4MP_EMAC1 field value from a register. */
#define ALT_L3_SEC_L4MP_EMAC1_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_L3_SEC_L4MP_EMAC1 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4MP_EMAC1_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : ACP ID Mapper Security - acpidmap
 * 
 * Controls whether secure or non-secure masters can access the ACP ID Mapper
 * slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description                                  
 * :-------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4MP_ACPIDMAP_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                     |       | master.                                      
 *  ALT_L3_SEC_L4MP_ACPIDMAP_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                     |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_ACPIDMAP
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4MP_ACPIDMAP_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_ACPIDMAP
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4MP_ACPIDMAP_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4MP_ACPIDMAP register field. */
#define ALT_L3_SEC_L4MP_ACPIDMAP_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4MP_ACPIDMAP register field. */
#define ALT_L3_SEC_L4MP_ACPIDMAP_MSB        6
/* The width in bits of the ALT_L3_SEC_L4MP_ACPIDMAP register field. */
#define ALT_L3_SEC_L4MP_ACPIDMAP_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4MP_ACPIDMAP register field value. */
#define ALT_L3_SEC_L4MP_ACPIDMAP_SET_MSK    0x00000040
/* The mask used to clear the ALT_L3_SEC_L4MP_ACPIDMAP register field value. */
#define ALT_L3_SEC_L4MP_ACPIDMAP_CLR_MSK    0xffffffbf
/* The reset value of the ALT_L3_SEC_L4MP_ACPIDMAP register field. */
#define ALT_L3_SEC_L4MP_ACPIDMAP_RESET      0x0
/* Extracts the ALT_L3_SEC_L4MP_ACPIDMAP field value from a register. */
#define ALT_L3_SEC_L4MP_ACPIDMAP_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_L3_SEC_L4MP_ACPIDMAP register field value suitable for setting the register. */
#define ALT_L3_SEC_L4MP_ACPIDMAP_SET(value) (((value) << 6) & 0x00000040)

/*
 * Field : GPIO 0 Security - gpio0
 * 
 * Controls whether secure or non-secure masters can access the GPIO 0 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                  
 * :----------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4MP_GPIO0_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                  |       | master.                                      
 *  ALT_L3_SEC_L4MP_GPIO0_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                  |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_GPIO0
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4MP_GPIO0_E_SECURE      0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_GPIO0
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4MP_GPIO0_E_NONSECURE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4MP_GPIO0 register field. */
#define ALT_L3_SEC_L4MP_GPIO0_LSB        7
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4MP_GPIO0 register field. */
#define ALT_L3_SEC_L4MP_GPIO0_MSB        7
/* The width in bits of the ALT_L3_SEC_L4MP_GPIO0 register field. */
#define ALT_L3_SEC_L4MP_GPIO0_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4MP_GPIO0 register field value. */
#define ALT_L3_SEC_L4MP_GPIO0_SET_MSK    0x00000080
/* The mask used to clear the ALT_L3_SEC_L4MP_GPIO0 register field value. */
#define ALT_L3_SEC_L4MP_GPIO0_CLR_MSK    0xffffff7f
/* The reset value of the ALT_L3_SEC_L4MP_GPIO0 register field. */
#define ALT_L3_SEC_L4MP_GPIO0_RESET      0x0
/* Extracts the ALT_L3_SEC_L4MP_GPIO0 field value from a register. */
#define ALT_L3_SEC_L4MP_GPIO0_GET(value) (((value) & 0x00000080) >> 7)
/* Produces a ALT_L3_SEC_L4MP_GPIO0 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4MP_GPIO0_SET(value) (((value) << 7) & 0x00000080)

/*
 * Field : GPIO 1 Security - gpio1
 * 
 * Controls whether secure or non-secure masters can access the GPIO 1 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                  
 * :----------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4MP_GPIO1_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                  |       | master.                                      
 *  ALT_L3_SEC_L4MP_GPIO1_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                  |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_GPIO1
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4MP_GPIO1_E_SECURE      0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_GPIO1
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4MP_GPIO1_E_NONSECURE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4MP_GPIO1 register field. */
#define ALT_L3_SEC_L4MP_GPIO1_LSB        8
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4MP_GPIO1 register field. */
#define ALT_L3_SEC_L4MP_GPIO1_MSB        8
/* The width in bits of the ALT_L3_SEC_L4MP_GPIO1 register field. */
#define ALT_L3_SEC_L4MP_GPIO1_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4MP_GPIO1 register field value. */
#define ALT_L3_SEC_L4MP_GPIO1_SET_MSK    0x00000100
/* The mask used to clear the ALT_L3_SEC_L4MP_GPIO1 register field value. */
#define ALT_L3_SEC_L4MP_GPIO1_CLR_MSK    0xfffffeff
/* The reset value of the ALT_L3_SEC_L4MP_GPIO1 register field. */
#define ALT_L3_SEC_L4MP_GPIO1_RESET      0x0
/* Extracts the ALT_L3_SEC_L4MP_GPIO1 field value from a register. */
#define ALT_L3_SEC_L4MP_GPIO1_GET(value) (((value) & 0x00000100) >> 8)
/* Produces a ALT_L3_SEC_L4MP_GPIO1 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4MP_GPIO1_SET(value) (((value) << 8) & 0x00000100)

/*
 * Field : GPIO 2 Security - gpio2
 * 
 * Controls whether secure or non-secure masters can access the GPIO 2 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                  
 * :----------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4MP_GPIO2_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                  |       | master.                                      
 *  ALT_L3_SEC_L4MP_GPIO2_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                  |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_GPIO2
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4MP_GPIO2_E_SECURE      0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4MP_GPIO2
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4MP_GPIO2_E_NONSECURE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4MP_GPIO2 register field. */
#define ALT_L3_SEC_L4MP_GPIO2_LSB        9
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4MP_GPIO2 register field. */
#define ALT_L3_SEC_L4MP_GPIO2_MSB        9
/* The width in bits of the ALT_L3_SEC_L4MP_GPIO2 register field. */
#define ALT_L3_SEC_L4MP_GPIO2_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4MP_GPIO2 register field value. */
#define ALT_L3_SEC_L4MP_GPIO2_SET_MSK    0x00000200
/* The mask used to clear the ALT_L3_SEC_L4MP_GPIO2 register field value. */
#define ALT_L3_SEC_L4MP_GPIO2_CLR_MSK    0xfffffdff
/* The reset value of the ALT_L3_SEC_L4MP_GPIO2 register field. */
#define ALT_L3_SEC_L4MP_GPIO2_RESET      0x0
/* Extracts the ALT_L3_SEC_L4MP_GPIO2 field value from a register. */
#define ALT_L3_SEC_L4MP_GPIO2_GET(value) (((value) & 0x00000200) >> 9)
/* Produces a ALT_L3_SEC_L4MP_GPIO2 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4MP_GPIO2_SET(value) (((value) << 9) & 0x00000200)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_L4MP.
 */
struct ALT_L3_SEC_L4MP_s
{
    uint32_t  fpgamgrregs :  1;  /* FPGA Manager Register Security */
    uint32_t  dap         :  1;  /* DAP Security */
    uint32_t  qspiregs    :  1;  /* QSPI Registers Security */
    uint32_t  sdmmc       :  1;  /* SDMMC Security */
    uint32_t  emac0       :  1;  /* EMAC 0 Security */
    uint32_t  emac1       :  1;  /* EMAC 1 Security */
    uint32_t  acpidmap    :  1;  /* ACP ID Mapper Security */
    uint32_t  gpio0       :  1;  /* GPIO 0 Security */
    uint32_t  gpio1       :  1;  /* GPIO 1 Security */
    uint32_t  gpio2       :  1;  /* GPIO 2 Security */
    uint32_t              : 22;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_L4MP. */
typedef volatile struct ALT_L3_SEC_L4MP_s  ALT_L3_SEC_L4MP_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_L4MP register from the beginning of the component. */
#define ALT_L3_SEC_L4MP_OFST        0x8

/*
 * Register : L4 OSC1 Peripherals Security - l4osc1
 * 
 * Controls security settings for L4 OSC1 peripherals.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                 
 * :-------|:-------|:------|:-----------------------------
 *  [0]    | W      | 0x0   | L4 Watchdog Timer 0 Security
 *  [1]    | W      | 0x0   | L4 Watchdog Timer 0 Security
 *  [2]    | W      | 0x0   | Clock Manager Security      
 *  [3]    | W      | 0x0   | Reset Manager Security      
 *  [4]    | W      | 0x0   | System Manager Security     
 *  [5]    | W      | 0x0   | OSC1 Timer 0 Security       
 *  [6]    | W      | 0x0   | OSC1 Timer 1 Security       
 *  [31:7] | ???    | 0x0   | *UNDEFINED*                 
 * 
 */
/*
 * Field : L4 Watchdog Timer 0 Security - l4wd0
 * 
 * Controls whether secure or non-secure masters can access the L4 Watchdog Timer 0
 * slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                                  
 * :------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4OSC1_L4WD0_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                    |       | master.                                      
 *  ALT_L3_SEC_L4OSC1_L4WD0_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                    |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4OSC1_L4WD0
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4OSC1_L4WD0_E_SECURE    0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4OSC1_L4WD0
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4OSC1_L4WD0_E_NONSECURE 0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4OSC1_L4WD0 register field. */
#define ALT_L3_SEC_L4OSC1_L4WD0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4OSC1_L4WD0 register field. */
#define ALT_L3_SEC_L4OSC1_L4WD0_MSB        0
/* The width in bits of the ALT_L3_SEC_L4OSC1_L4WD0 register field. */
#define ALT_L3_SEC_L4OSC1_L4WD0_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4OSC1_L4WD0 register field value. */
#define ALT_L3_SEC_L4OSC1_L4WD0_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_L4OSC1_L4WD0 register field value. */
#define ALT_L3_SEC_L4OSC1_L4WD0_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_L4OSC1_L4WD0 register field. */
#define ALT_L3_SEC_L4OSC1_L4WD0_RESET      0x0
/* Extracts the ALT_L3_SEC_L4OSC1_L4WD0 field value from a register. */
#define ALT_L3_SEC_L4OSC1_L4WD0_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_L4OSC1_L4WD0 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4OSC1_L4WD0_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : L4 Watchdog Timer 0 Security - l4wd1
 * 
 * Controls whether secure or non-secure masters can access the L4 Watchdog Timer 0
 * slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                                  
 * :------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4OSC1_L4WD1_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                    |       | master.                                      
 *  ALT_L3_SEC_L4OSC1_L4WD1_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                    |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4OSC1_L4WD1
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4OSC1_L4WD1_E_SECURE    0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4OSC1_L4WD1
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4OSC1_L4WD1_E_NONSECURE 0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4OSC1_L4WD1 register field. */
#define ALT_L3_SEC_L4OSC1_L4WD1_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4OSC1_L4WD1 register field. */
#define ALT_L3_SEC_L4OSC1_L4WD1_MSB        1
/* The width in bits of the ALT_L3_SEC_L4OSC1_L4WD1 register field. */
#define ALT_L3_SEC_L4OSC1_L4WD1_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4OSC1_L4WD1 register field value. */
#define ALT_L3_SEC_L4OSC1_L4WD1_SET_MSK    0x00000002
/* The mask used to clear the ALT_L3_SEC_L4OSC1_L4WD1 register field value. */
#define ALT_L3_SEC_L4OSC1_L4WD1_CLR_MSK    0xfffffffd
/* The reset value of the ALT_L3_SEC_L4OSC1_L4WD1 register field. */
#define ALT_L3_SEC_L4OSC1_L4WD1_RESET      0x0
/* Extracts the ALT_L3_SEC_L4OSC1_L4WD1 field value from a register. */
#define ALT_L3_SEC_L4OSC1_L4WD1_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_L3_SEC_L4OSC1_L4WD1 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4OSC1_L4WD1_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Clock Manager Security - clkmgr
 * 
 * Controls whether secure or non-secure masters can access the Clock Manager
 * slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description                                  
 * :-------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4OSC1_CLKMGR_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                     |       | master.                                      
 *  ALT_L3_SEC_L4OSC1_CLKMGR_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                     |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4OSC1_CLKMGR
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4OSC1_CLKMGR_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4OSC1_CLKMGR
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4OSC1_CLKMGR_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4OSC1_CLKMGR register field. */
#define ALT_L3_SEC_L4OSC1_CLKMGR_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4OSC1_CLKMGR register field. */
#define ALT_L3_SEC_L4OSC1_CLKMGR_MSB        2
/* The width in bits of the ALT_L3_SEC_L4OSC1_CLKMGR register field. */
#define ALT_L3_SEC_L4OSC1_CLKMGR_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4OSC1_CLKMGR register field value. */
#define ALT_L3_SEC_L4OSC1_CLKMGR_SET_MSK    0x00000004
/* The mask used to clear the ALT_L3_SEC_L4OSC1_CLKMGR register field value. */
#define ALT_L3_SEC_L4OSC1_CLKMGR_CLR_MSK    0xfffffffb
/* The reset value of the ALT_L3_SEC_L4OSC1_CLKMGR register field. */
#define ALT_L3_SEC_L4OSC1_CLKMGR_RESET      0x0
/* Extracts the ALT_L3_SEC_L4OSC1_CLKMGR field value from a register. */
#define ALT_L3_SEC_L4OSC1_CLKMGR_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_L3_SEC_L4OSC1_CLKMGR register field value suitable for setting the register. */
#define ALT_L3_SEC_L4OSC1_CLKMGR_SET(value) (((value) << 2) & 0x00000004)

/*
 * Field : Reset Manager Security - rstmgr
 * 
 * Controls whether secure or non-secure masters can access the Reset Manager
 * slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description                                  
 * :-------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4OSC1_RSTMGR_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                     |       | master.                                      
 *  ALT_L3_SEC_L4OSC1_RSTMGR_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                     |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4OSC1_RSTMGR
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4OSC1_RSTMGR_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4OSC1_RSTMGR
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4OSC1_RSTMGR_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4OSC1_RSTMGR register field. */
#define ALT_L3_SEC_L4OSC1_RSTMGR_LSB        3
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4OSC1_RSTMGR register field. */
#define ALT_L3_SEC_L4OSC1_RSTMGR_MSB        3
/* The width in bits of the ALT_L3_SEC_L4OSC1_RSTMGR register field. */
#define ALT_L3_SEC_L4OSC1_RSTMGR_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4OSC1_RSTMGR register field value. */
#define ALT_L3_SEC_L4OSC1_RSTMGR_SET_MSK    0x00000008
/* The mask used to clear the ALT_L3_SEC_L4OSC1_RSTMGR register field value. */
#define ALT_L3_SEC_L4OSC1_RSTMGR_CLR_MSK    0xfffffff7
/* The reset value of the ALT_L3_SEC_L4OSC1_RSTMGR register field. */
#define ALT_L3_SEC_L4OSC1_RSTMGR_RESET      0x0
/* Extracts the ALT_L3_SEC_L4OSC1_RSTMGR field value from a register. */
#define ALT_L3_SEC_L4OSC1_RSTMGR_GET(value) (((value) & 0x00000008) >> 3)
/* Produces a ALT_L3_SEC_L4OSC1_RSTMGR register field value suitable for setting the register. */
#define ALT_L3_SEC_L4OSC1_RSTMGR_SET(value) (((value) << 3) & 0x00000008)

/*
 * Field : System Manager Security - sysmgr
 * 
 * Controls whether secure or non-secure masters can access the System Manager
 * slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description                                  
 * :-------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4OSC1_SYSMGR_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                     |       | master.                                      
 *  ALT_L3_SEC_L4OSC1_SYSMGR_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                     |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4OSC1_SYSMGR
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4OSC1_SYSMGR_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4OSC1_SYSMGR
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4OSC1_SYSMGR_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4OSC1_SYSMGR register field. */
#define ALT_L3_SEC_L4OSC1_SYSMGR_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4OSC1_SYSMGR register field. */
#define ALT_L3_SEC_L4OSC1_SYSMGR_MSB        4
/* The width in bits of the ALT_L3_SEC_L4OSC1_SYSMGR register field. */
#define ALT_L3_SEC_L4OSC1_SYSMGR_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4OSC1_SYSMGR register field value. */
#define ALT_L3_SEC_L4OSC1_SYSMGR_SET_MSK    0x00000010
/* The mask used to clear the ALT_L3_SEC_L4OSC1_SYSMGR register field value. */
#define ALT_L3_SEC_L4OSC1_SYSMGR_CLR_MSK    0xffffffef
/* The reset value of the ALT_L3_SEC_L4OSC1_SYSMGR register field. */
#define ALT_L3_SEC_L4OSC1_SYSMGR_RESET      0x0
/* Extracts the ALT_L3_SEC_L4OSC1_SYSMGR field value from a register. */
#define ALT_L3_SEC_L4OSC1_SYSMGR_GET(value) (((value) & 0x00000010) >> 4)
/* Produces a ALT_L3_SEC_L4OSC1_SYSMGR register field value suitable for setting the register. */
#define ALT_L3_SEC_L4OSC1_SYSMGR_SET(value) (((value) << 4) & 0x00000010)

/*
 * Field : OSC1 Timer 0 Security - osc1timer0
 * 
 * Controls whether secure or non-secure masters can access the OSC1 Timer 0 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description                                  
 * :---------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4OSC1_OSC1TMR0_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                       |       | master.                                      
 *  ALT_L3_SEC_L4OSC1_OSC1TMR0_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                       |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4OSC1_OSC1TMR0
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4OSC1_OSC1TMR0_E_SECURE     0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4OSC1_OSC1TMR0
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4OSC1_OSC1TMR0_E_NONSECURE  0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4OSC1_OSC1TMR0 register field. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR0_LSB        5
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4OSC1_OSC1TMR0 register field. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR0_MSB        5
/* The width in bits of the ALT_L3_SEC_L4OSC1_OSC1TMR0 register field. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR0_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4OSC1_OSC1TMR0 register field value. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR0_SET_MSK    0x00000020
/* The mask used to clear the ALT_L3_SEC_L4OSC1_OSC1TMR0 register field value. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR0_CLR_MSK    0xffffffdf
/* The reset value of the ALT_L3_SEC_L4OSC1_OSC1TMR0 register field. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR0_RESET      0x0
/* Extracts the ALT_L3_SEC_L4OSC1_OSC1TMR0 field value from a register. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR0_GET(value) (((value) & 0x00000020) >> 5)
/* Produces a ALT_L3_SEC_L4OSC1_OSC1TMR0 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR0_SET(value) (((value) << 5) & 0x00000020)

/*
 * Field : OSC1 Timer 1 Security - osc1timer1
 * 
 * Controls whether secure or non-secure masters can access the OSC1 Timer 1 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                   | Value | Description                                  
 * :---------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4OSC1_OSC1TMR1_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                       |       | master.                                      
 *  ALT_L3_SEC_L4OSC1_OSC1TMR1_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                       |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4OSC1_OSC1TMR1
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4OSC1_OSC1TMR1_E_SECURE     0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4OSC1_OSC1TMR1
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4OSC1_OSC1TMR1_E_NONSECURE  0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4OSC1_OSC1TMR1 register field. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR1_LSB        6
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4OSC1_OSC1TMR1 register field. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR1_MSB        6
/* The width in bits of the ALT_L3_SEC_L4OSC1_OSC1TMR1 register field. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR1_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4OSC1_OSC1TMR1 register field value. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR1_SET_MSK    0x00000040
/* The mask used to clear the ALT_L3_SEC_L4OSC1_OSC1TMR1 register field value. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR1_CLR_MSK    0xffffffbf
/* The reset value of the ALT_L3_SEC_L4OSC1_OSC1TMR1 register field. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR1_RESET      0x0
/* Extracts the ALT_L3_SEC_L4OSC1_OSC1TMR1 field value from a register. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR1_GET(value) (((value) & 0x00000040) >> 6)
/* Produces a ALT_L3_SEC_L4OSC1_OSC1TMR1 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4OSC1_OSC1TMR1_SET(value) (((value) << 6) & 0x00000040)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_L4OSC1.
 */
struct ALT_L3_SEC_L4OSC1_s
{
    uint32_t  l4wd0      :  1;  /* L4 Watchdog Timer 0 Security */
    uint32_t  l4wd1      :  1;  /* L4 Watchdog Timer 0 Security */
    uint32_t  clkmgr     :  1;  /* Clock Manager Security */
    uint32_t  rstmgr     :  1;  /* Reset Manager Security */
    uint32_t  sysmgr     :  1;  /* System Manager Security */
    uint32_t  osc1timer0 :  1;  /* OSC1 Timer 0 Security */
    uint32_t  osc1timer1 :  1;  /* OSC1 Timer 1 Security */
    uint32_t             : 25;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_L4OSC1. */
typedef volatile struct ALT_L3_SEC_L4OSC1_s  ALT_L3_SEC_L4OSC1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_L4OSC1 register from the beginning of the component. */
#define ALT_L3_SEC_L4OSC1_OFST        0xc

/*
 * Register : L4 SPIM Peripherals Security - l4spim
 * 
 * Controls security settings for L4 SPIM peripherals.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description          
 * :-------|:-------|:------|:----------------------
 *  [0]    | W      | 0x0   | SPI Master 0 Security
 *  [1]    | W      | 0x0   | SPI Master 1 Security
 *  [2]    | W      | 0x0   | Scan Manager Security
 *  [31:3] | ???    | 0x0   | *UNDEFINED*          
 * 
 */
/*
 * Field : SPI Master 0 Security - spim0
 * 
 * Controls whether secure or non-secure masters can access the SPI Master 0 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                                  
 * :------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4SPIM_SPIM0_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                    |       | master.                                      
 *  ALT_L3_SEC_L4SPIM_SPIM0_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                    |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4SPIM_SPIM0
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4SPIM_SPIM0_E_SECURE    0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4SPIM_SPIM0
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4SPIM_SPIM0_E_NONSECURE 0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4SPIM_SPIM0 register field. */
#define ALT_L3_SEC_L4SPIM_SPIM0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4SPIM_SPIM0 register field. */
#define ALT_L3_SEC_L4SPIM_SPIM0_MSB        0
/* The width in bits of the ALT_L3_SEC_L4SPIM_SPIM0 register field. */
#define ALT_L3_SEC_L4SPIM_SPIM0_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4SPIM_SPIM0 register field value. */
#define ALT_L3_SEC_L4SPIM_SPIM0_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_L4SPIM_SPIM0 register field value. */
#define ALT_L3_SEC_L4SPIM_SPIM0_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_L4SPIM_SPIM0 register field. */
#define ALT_L3_SEC_L4SPIM_SPIM0_RESET      0x0
/* Extracts the ALT_L3_SEC_L4SPIM_SPIM0 field value from a register. */
#define ALT_L3_SEC_L4SPIM_SPIM0_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_L4SPIM_SPIM0 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4SPIM_SPIM0_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : SPI Master 1 Security - spim1
 * 
 * Controls whether secure or non-secure masters can access the SPI Master 1 slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                | Value | Description                                  
 * :------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4SPIM_SPIM1_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                    |       | master.                                      
 *  ALT_L3_SEC_L4SPIM_SPIM1_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                    |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4SPIM_SPIM1
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4SPIM_SPIM1_E_SECURE    0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4SPIM_SPIM1
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4SPIM_SPIM1_E_NONSECURE 0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4SPIM_SPIM1 register field. */
#define ALT_L3_SEC_L4SPIM_SPIM1_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4SPIM_SPIM1 register field. */
#define ALT_L3_SEC_L4SPIM_SPIM1_MSB        1
/* The width in bits of the ALT_L3_SEC_L4SPIM_SPIM1 register field. */
#define ALT_L3_SEC_L4SPIM_SPIM1_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4SPIM_SPIM1 register field value. */
#define ALT_L3_SEC_L4SPIM_SPIM1_SET_MSK    0x00000002
/* The mask used to clear the ALT_L3_SEC_L4SPIM_SPIM1 register field value. */
#define ALT_L3_SEC_L4SPIM_SPIM1_CLR_MSK    0xfffffffd
/* The reset value of the ALT_L3_SEC_L4SPIM_SPIM1 register field. */
#define ALT_L3_SEC_L4SPIM_SPIM1_RESET      0x0
/* Extracts the ALT_L3_SEC_L4SPIM_SPIM1 field value from a register. */
#define ALT_L3_SEC_L4SPIM_SPIM1_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_L3_SEC_L4SPIM_SPIM1 register field value suitable for setting the register. */
#define ALT_L3_SEC_L4SPIM_SPIM1_SET(value) (((value) << 1) & 0x00000002)

/*
 * Field : Scan Manager Security - scanmgr
 * 
 * Controls whether secure or non-secure masters can access the Scan Manager slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description                                  
 * :--------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_L4SPIM_SCANMGR_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                      |       | master.                                      
 *  ALT_L3_SEC_L4SPIM_SCANMGR_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                      |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_L4SPIM_SCANMGR
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_L4SPIM_SCANMGR_E_SECURE      0x0
/*
 * Enumerated value for register field ALT_L3_SEC_L4SPIM_SCANMGR
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_L4SPIM_SCANMGR_E_NONSECURE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_L4SPIM_SCANMGR register field. */
#define ALT_L3_SEC_L4SPIM_SCANMGR_LSB        2
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_L4SPIM_SCANMGR register field. */
#define ALT_L3_SEC_L4SPIM_SCANMGR_MSB        2
/* The width in bits of the ALT_L3_SEC_L4SPIM_SCANMGR register field. */
#define ALT_L3_SEC_L4SPIM_SCANMGR_WIDTH      1
/* The mask used to set the ALT_L3_SEC_L4SPIM_SCANMGR register field value. */
#define ALT_L3_SEC_L4SPIM_SCANMGR_SET_MSK    0x00000004
/* The mask used to clear the ALT_L3_SEC_L4SPIM_SCANMGR register field value. */
#define ALT_L3_SEC_L4SPIM_SCANMGR_CLR_MSK    0xfffffffb
/* The reset value of the ALT_L3_SEC_L4SPIM_SCANMGR register field. */
#define ALT_L3_SEC_L4SPIM_SCANMGR_RESET      0x0
/* Extracts the ALT_L3_SEC_L4SPIM_SCANMGR field value from a register. */
#define ALT_L3_SEC_L4SPIM_SCANMGR_GET(value) (((value) & 0x00000004) >> 2)
/* Produces a ALT_L3_SEC_L4SPIM_SCANMGR register field value suitable for setting the register. */
#define ALT_L3_SEC_L4SPIM_SCANMGR_SET(value) (((value) << 2) & 0x00000004)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_L4SPIM.
 */
struct ALT_L3_SEC_L4SPIM_s
{
    uint32_t  spim0   :  1;  /* SPI Master 0 Security */
    uint32_t  spim1   :  1;  /* SPI Master 1 Security */
    uint32_t  scanmgr :  1;  /* Scan Manager Security */
    uint32_t          : 29;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_L4SPIM. */
typedef volatile struct ALT_L3_SEC_L4SPIM_s  ALT_L3_SEC_L4SPIM_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_L4SPIM register from the beginning of the component. */
#define ALT_L3_SEC_L4SPIM_OFST        0x10

/*
 * Register : STM Peripheral Security - stm
 * 
 * Controls security settings for STM peripheral.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description 
 * :-------|:-------|:------|:-------------
 *  [0]    | W      | 0x0   | STM Security
 *  [31:1] | ???    | 0x0   | *UNDEFINED* 
 * 
 */
/*
 * Field : STM Security - s
 * 
 * Controls whether secure or non-secure masters can access the STM slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description                                  
 * :-----------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_STM_S_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                             |       | master.                                      
 *  ALT_L3_SEC_STM_S_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                             |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_STM_S
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_STM_S_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_STM_S
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_STM_S_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_STM_S register field. */
#define ALT_L3_SEC_STM_S_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_STM_S register field. */
#define ALT_L3_SEC_STM_S_MSB        0
/* The width in bits of the ALT_L3_SEC_STM_S register field. */
#define ALT_L3_SEC_STM_S_WIDTH      1
/* The mask used to set the ALT_L3_SEC_STM_S register field value. */
#define ALT_L3_SEC_STM_S_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_STM_S register field value. */
#define ALT_L3_SEC_STM_S_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_STM_S register field. */
#define ALT_L3_SEC_STM_S_RESET      0x0
/* Extracts the ALT_L3_SEC_STM_S field value from a register. */
#define ALT_L3_SEC_STM_S_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_STM_S register field value suitable for setting the register. */
#define ALT_L3_SEC_STM_S_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_STM.
 */
struct ALT_L3_SEC_STM_s
{
    uint32_t  s :  1;  /* STM Security */
    uint32_t    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_STM. */
typedef volatile struct ALT_L3_SEC_STM_s  ALT_L3_SEC_STM_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_STM register from the beginning of the component. */
#define ALT_L3_SEC_STM_OFST        0x14

/*
 * Register : LWHPS2FPGA AXI Bridge Registers Peripheral Security - lwhps2fpgaregs
 * 
 * Controls security settings for LWHPS2FPGA AXI Bridge Registers peripheral.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                             
 * :-------|:-------|:------|:-----------------------------------------
 *  [0]    | W      | 0x0   | LWHPS2FPGA AXI Bridge Registers Security
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                             
 * 
 */
/*
 * Field : LWHPS2FPGA AXI Bridge Registers Security - s
 * 
 * Controls whether secure or non-secure masters can access the LWHPS2FPGA AXI
 * Bridge Registers slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description                                  
 * :-------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_LWH2F_S_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                               |       | master.                                      
 *  ALT_L3_SEC_LWH2F_S_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                               |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_LWH2F_S
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_LWH2F_S_E_SECURE     0x0
/*
 * Enumerated value for register field ALT_L3_SEC_LWH2F_S
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_LWH2F_S_E_NONSECURE  0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_LWH2F_S register field. */
#define ALT_L3_SEC_LWH2F_S_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_LWH2F_S register field. */
#define ALT_L3_SEC_LWH2F_S_MSB        0
/* The width in bits of the ALT_L3_SEC_LWH2F_S register field. */
#define ALT_L3_SEC_LWH2F_S_WIDTH      1
/* The mask used to set the ALT_L3_SEC_LWH2F_S register field value. */
#define ALT_L3_SEC_LWH2F_S_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_LWH2F_S register field value. */
#define ALT_L3_SEC_LWH2F_S_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_LWH2F_S register field. */
#define ALT_L3_SEC_LWH2F_S_RESET      0x0
/* Extracts the ALT_L3_SEC_LWH2F_S field value from a register. */
#define ALT_L3_SEC_LWH2F_S_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_LWH2F_S register field value suitable for setting the register. */
#define ALT_L3_SEC_LWH2F_S_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_LWH2F.
 */
struct ALT_L3_SEC_LWH2F_s
{
    uint32_t  s :  1;  /* LWHPS2FPGA AXI Bridge Registers Security */
    uint32_t    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_LWH2F. */
typedef volatile struct ALT_L3_SEC_LWH2F_s  ALT_L3_SEC_LWH2F_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_LWH2F register from the beginning of the component. */
#define ALT_L3_SEC_LWH2F_OFST        0x18

/*
 * Register : USB1 Registers Peripheral Security - usb1
 * 
 * Controls security settings for USB1 Registers peripheral.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description            
 * :-------|:-------|:------|:------------------------
 *  [0]    | W      | 0x0   | USB1 Registers Security
 *  [31:1] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : USB1 Registers Security - s
 * 
 * Controls whether secure or non-secure masters can access the USB1 Registers
 * slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                                  
 * :------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_USB1_S_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                              |       | master.                                      
 *  ALT_L3_SEC_USB1_S_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                              |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_USB1_S
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_USB1_S_E_SECURE      0x0
/*
 * Enumerated value for register field ALT_L3_SEC_USB1_S
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_USB1_S_E_NONSECURE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_USB1_S register field. */
#define ALT_L3_SEC_USB1_S_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_USB1_S register field. */
#define ALT_L3_SEC_USB1_S_MSB        0
/* The width in bits of the ALT_L3_SEC_USB1_S register field. */
#define ALT_L3_SEC_USB1_S_WIDTH      1
/* The mask used to set the ALT_L3_SEC_USB1_S register field value. */
#define ALT_L3_SEC_USB1_S_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_USB1_S register field value. */
#define ALT_L3_SEC_USB1_S_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_USB1_S register field. */
#define ALT_L3_SEC_USB1_S_RESET      0x0
/* Extracts the ALT_L3_SEC_USB1_S field value from a register. */
#define ALT_L3_SEC_USB1_S_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_USB1_S register field value suitable for setting the register. */
#define ALT_L3_SEC_USB1_S_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_USB1.
 */
struct ALT_L3_SEC_USB1_s
{
    uint32_t  s :  1;  /* USB1 Registers Security */
    uint32_t    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_USB1. */
typedef volatile struct ALT_L3_SEC_USB1_s  ALT_L3_SEC_USB1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_USB1 register from the beginning of the component. */
#define ALT_L3_SEC_USB1_OFST        0x20

/*
 * Register : NAND Flash Controller Data Peripheral Security - nanddata
 * 
 * Controls security settings for NAND Flash Controller Data peripheral.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                        
 * :-------|:-------|:------|:------------------------------------
 *  [0]    | W      | 0x0   | NAND Flash Controller Data Security
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : NAND Flash Controller Data Security - s
 * 
 * Controls whether secure or non-secure masters can access the NAND Flash
 * Controller Data slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                  
 * :----------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_NANDDATA_S_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                  |       | master.                                      
 *  ALT_L3_SEC_NANDDATA_S_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                  |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_NANDDATA_S
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_NANDDATA_S_E_SECURE      0x0
/*
 * Enumerated value for register field ALT_L3_SEC_NANDDATA_S
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_NANDDATA_S_E_NONSECURE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_NANDDATA_S register field. */
#define ALT_L3_SEC_NANDDATA_S_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_NANDDATA_S register field. */
#define ALT_L3_SEC_NANDDATA_S_MSB        0
/* The width in bits of the ALT_L3_SEC_NANDDATA_S register field. */
#define ALT_L3_SEC_NANDDATA_S_WIDTH      1
/* The mask used to set the ALT_L3_SEC_NANDDATA_S register field value. */
#define ALT_L3_SEC_NANDDATA_S_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_NANDDATA_S register field value. */
#define ALT_L3_SEC_NANDDATA_S_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_NANDDATA_S register field. */
#define ALT_L3_SEC_NANDDATA_S_RESET      0x0
/* Extracts the ALT_L3_SEC_NANDDATA_S field value from a register. */
#define ALT_L3_SEC_NANDDATA_S_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_NANDDATA_S register field value suitable for setting the register. */
#define ALT_L3_SEC_NANDDATA_S_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_NANDDATA.
 */
struct ALT_L3_SEC_NANDDATA_s
{
    uint32_t  s :  1;  /* NAND Flash Controller Data Security */
    uint32_t    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_NANDDATA. */
typedef volatile struct ALT_L3_SEC_NANDDATA_s  ALT_L3_SEC_NANDDATA_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_NANDDATA register from the beginning of the component. */
#define ALT_L3_SEC_NANDDATA_OFST        0x24

/*
 * Register : USB0 Registers Peripheral Security - usb0
 * 
 * Controls security settings for USB0 Registers peripheral.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description            
 * :-------|:-------|:------|:------------------------
 *  [0]    | W      | 0x0   | USB0 Registers Security
 *  [31:1] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : USB0 Registers Security - s
 * 
 * Controls whether secure or non-secure masters can access the USB0 Registers
 * slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                                  
 * :------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_USB0_S_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                              |       | master.                                      
 *  ALT_L3_SEC_USB0_S_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                              |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_USB0_S
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_USB0_S_E_SECURE      0x0
/*
 * Enumerated value for register field ALT_L3_SEC_USB0_S
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_USB0_S_E_NONSECURE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_USB0_S register field. */
#define ALT_L3_SEC_USB0_S_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_USB0_S register field. */
#define ALT_L3_SEC_USB0_S_MSB        0
/* The width in bits of the ALT_L3_SEC_USB0_S register field. */
#define ALT_L3_SEC_USB0_S_WIDTH      1
/* The mask used to set the ALT_L3_SEC_USB0_S register field value. */
#define ALT_L3_SEC_USB0_S_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_USB0_S register field value. */
#define ALT_L3_SEC_USB0_S_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_USB0_S register field. */
#define ALT_L3_SEC_USB0_S_RESET      0x0
/* Extracts the ALT_L3_SEC_USB0_S field value from a register. */
#define ALT_L3_SEC_USB0_S_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_USB0_S register field value suitable for setting the register. */
#define ALT_L3_SEC_USB0_S_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_USB0.
 */
struct ALT_L3_SEC_USB0_s
{
    uint32_t  s :  1;  /* USB0 Registers Security */
    uint32_t    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_USB0. */
typedef volatile struct ALT_L3_SEC_USB0_s  ALT_L3_SEC_USB0_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_USB0 register from the beginning of the component. */
#define ALT_L3_SEC_USB0_OFST        0x78

/*
 * Register : NAND Flash Controller Registers Peripheral Security - nandregs
 * 
 * Controls security settings for NAND Flash Controller Registers peripheral.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                             
 * :-------|:-------|:------|:-----------------------------------------
 *  [0]    | W      | 0x0   | NAND Flash Controller Registers Security
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                             
 * 
 */
/*
 * Field : NAND Flash Controller Registers Security - s
 * 
 * Controls whether secure or non-secure masters can access the NAND Flash
 * Controller Registers slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                          | Value | Description                                  
 * :------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_NAND_S_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                              |       | master.                                      
 *  ALT_L3_SEC_NAND_S_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                              |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_NAND_S
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_NAND_S_E_SECURE      0x0
/*
 * Enumerated value for register field ALT_L3_SEC_NAND_S
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_NAND_S_E_NONSECURE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_NAND_S register field. */
#define ALT_L3_SEC_NAND_S_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_NAND_S register field. */
#define ALT_L3_SEC_NAND_S_MSB        0
/* The width in bits of the ALT_L3_SEC_NAND_S register field. */
#define ALT_L3_SEC_NAND_S_WIDTH      1
/* The mask used to set the ALT_L3_SEC_NAND_S register field value. */
#define ALT_L3_SEC_NAND_S_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_NAND_S register field value. */
#define ALT_L3_SEC_NAND_S_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_NAND_S register field. */
#define ALT_L3_SEC_NAND_S_RESET      0x0
/* Extracts the ALT_L3_SEC_NAND_S field value from a register. */
#define ALT_L3_SEC_NAND_S_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_NAND_S register field value suitable for setting the register. */
#define ALT_L3_SEC_NAND_S_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_NAND.
 */
struct ALT_L3_SEC_NAND_s
{
    uint32_t  s :  1;  /* NAND Flash Controller Registers Security */
    uint32_t    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_NAND. */
typedef volatile struct ALT_L3_SEC_NAND_s  ALT_L3_SEC_NAND_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_NAND register from the beginning of the component. */
#define ALT_L3_SEC_NAND_OFST        0x7c

/*
 * Register : QSPI Flash Controller Data Peripheral Security - qspidata
 * 
 * Controls security settings for QSPI Flash Controller Data peripheral.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                        
 * :-------|:-------|:------|:------------------------------------
 *  [0]    | W      | 0x0   | QSPI Flash Controller Data Security
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                        
 * 
 */
/*
 * Field : QSPI Flash Controller Data Security - s
 * 
 * Controls whether secure or non-secure masters can access the QSPI Flash
 * Controller Data slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                              | Value | Description                                  
 * :----------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_QSPIDATA_S_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                  |       | master.                                      
 *  ALT_L3_SEC_QSPIDATA_S_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                  |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_QSPIDATA_S
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_QSPIDATA_S_E_SECURE      0x0
/*
 * Enumerated value for register field ALT_L3_SEC_QSPIDATA_S
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_QSPIDATA_S_E_NONSECURE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_QSPIDATA_S register field. */
#define ALT_L3_SEC_QSPIDATA_S_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_QSPIDATA_S register field. */
#define ALT_L3_SEC_QSPIDATA_S_MSB        0
/* The width in bits of the ALT_L3_SEC_QSPIDATA_S register field. */
#define ALT_L3_SEC_QSPIDATA_S_WIDTH      1
/* The mask used to set the ALT_L3_SEC_QSPIDATA_S register field value. */
#define ALT_L3_SEC_QSPIDATA_S_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_QSPIDATA_S register field value. */
#define ALT_L3_SEC_QSPIDATA_S_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_QSPIDATA_S register field. */
#define ALT_L3_SEC_QSPIDATA_S_RESET      0x0
/* Extracts the ALT_L3_SEC_QSPIDATA_S field value from a register. */
#define ALT_L3_SEC_QSPIDATA_S_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_QSPIDATA_S register field value suitable for setting the register. */
#define ALT_L3_SEC_QSPIDATA_S_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_QSPIDATA.
 */
struct ALT_L3_SEC_QSPIDATA_s
{
    uint32_t  s :  1;  /* QSPI Flash Controller Data Security */
    uint32_t    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_QSPIDATA. */
typedef volatile struct ALT_L3_SEC_QSPIDATA_s  ALT_L3_SEC_QSPIDATA_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_QSPIDATA register from the beginning of the component. */
#define ALT_L3_SEC_QSPIDATA_OFST        0x80

/*
 * Register : FPGA Manager Data Peripheral Security - fpgamgrdata
 * 
 * Controls security settings for FPGA Manager Data peripheral.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description               
 * :-------|:-------|:------|:---------------------------
 *  [0]    | W      | 0x0   | FPGA Manager Data Security
 *  [31:1] | ???    | 0x0   | *UNDEFINED*               
 * 
 */
/*
 * Field : FPGA Manager Data Security - s
 * 
 * Controls whether secure or non-secure masters can access the FPGA Manager Data
 * slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                 | Value | Description                                  
 * :-------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_FPGAMGRDATA_S_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                     |       | master.                                      
 *  ALT_L3_SEC_FPGAMGRDATA_S_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                     |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_FPGAMGRDATA_S
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_FPGAMGRDATA_S_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_FPGAMGRDATA_S
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_FPGAMGRDATA_S_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_FPGAMGRDATA_S register field. */
#define ALT_L3_SEC_FPGAMGRDATA_S_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_FPGAMGRDATA_S register field. */
#define ALT_L3_SEC_FPGAMGRDATA_S_MSB        0
/* The width in bits of the ALT_L3_SEC_FPGAMGRDATA_S register field. */
#define ALT_L3_SEC_FPGAMGRDATA_S_WIDTH      1
/* The mask used to set the ALT_L3_SEC_FPGAMGRDATA_S register field value. */
#define ALT_L3_SEC_FPGAMGRDATA_S_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_FPGAMGRDATA_S register field value. */
#define ALT_L3_SEC_FPGAMGRDATA_S_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_FPGAMGRDATA_S register field. */
#define ALT_L3_SEC_FPGAMGRDATA_S_RESET      0x0
/* Extracts the ALT_L3_SEC_FPGAMGRDATA_S field value from a register. */
#define ALT_L3_SEC_FPGAMGRDATA_S_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_FPGAMGRDATA_S register field value suitable for setting the register. */
#define ALT_L3_SEC_FPGAMGRDATA_S_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_FPGAMGRDATA.
 */
struct ALT_L3_SEC_FPGAMGRDATA_s
{
    uint32_t  s :  1;  /* FPGA Manager Data Security */
    uint32_t    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_FPGAMGRDATA. */
typedef volatile struct ALT_L3_SEC_FPGAMGRDATA_s  ALT_L3_SEC_FPGAMGRDATA_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_FPGAMGRDATA register from the beginning of the component. */
#define ALT_L3_SEC_FPGAMGRDATA_OFST        0x84

/*
 * Register : HPS2FPGA AXI Bridge Registers Peripheral Security - hps2fpgaregs
 * 
 * Controls security settings for HPS2FPGA AXI Bridge Registers peripheral.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description                           
 * :-------|:-------|:------|:---------------------------------------
 *  [0]    | W      | 0x0   | HPS2FPGA AXI Bridge Registers Security
 *  [31:1] | ???    | 0x0   | *UNDEFINED*                           
 * 
 */
/*
 * Field : HPS2FPGA AXI Bridge Registers Security - s
 * 
 * Controls whether secure or non-secure masters can access the HPS2FPGA AXI Bridge
 * Registers slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description                                  
 * :-----------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_H2F_S_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                             |       | master.                                      
 *  ALT_L3_SEC_H2F_S_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                             |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_H2F_S
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_H2F_S_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_H2F_S
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_H2F_S_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_H2F_S register field. */
#define ALT_L3_SEC_H2F_S_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_H2F_S register field. */
#define ALT_L3_SEC_H2F_S_MSB        0
/* The width in bits of the ALT_L3_SEC_H2F_S register field. */
#define ALT_L3_SEC_H2F_S_WIDTH      1
/* The mask used to set the ALT_L3_SEC_H2F_S register field value. */
#define ALT_L3_SEC_H2F_S_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_H2F_S register field value. */
#define ALT_L3_SEC_H2F_S_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_H2F_S register field. */
#define ALT_L3_SEC_H2F_S_RESET      0x0
/* Extracts the ALT_L3_SEC_H2F_S field value from a register. */
#define ALT_L3_SEC_H2F_S_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_H2F_S register field value suitable for setting the register. */
#define ALT_L3_SEC_H2F_S_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_H2F.
 */
struct ALT_L3_SEC_H2F_s
{
    uint32_t  s :  1;  /* HPS2FPGA AXI Bridge Registers Security */
    uint32_t    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_H2F. */
typedef volatile struct ALT_L3_SEC_H2F_s  ALT_L3_SEC_H2F_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_H2F register from the beginning of the component. */
#define ALT_L3_SEC_H2F_OFST        0x88

/*
 * Register : MPU ACP Peripheral Security - acp
 * 
 * Controls security settings for MPU ACP peripheral.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description     
 * :-------|:-------|:------|:-----------------
 *  [0]    | W      | 0x0   | MPU ACP Security
 *  [31:1] | ???    | 0x0   | *UNDEFINED*     
 * 
 */
/*
 * Field : MPU ACP Security - s
 * 
 * Controls whether secure or non-secure masters can access the MPU ACP slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description                                  
 * :-----------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_ACP_S_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                             |       | master.                                      
 *  ALT_L3_SEC_ACP_S_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                             |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_ACP_S
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_ACP_S_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_ACP_S
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_ACP_S_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_ACP_S register field. */
#define ALT_L3_SEC_ACP_S_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_ACP_S register field. */
#define ALT_L3_SEC_ACP_S_MSB        0
/* The width in bits of the ALT_L3_SEC_ACP_S register field. */
#define ALT_L3_SEC_ACP_S_WIDTH      1
/* The mask used to set the ALT_L3_SEC_ACP_S register field value. */
#define ALT_L3_SEC_ACP_S_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_ACP_S register field value. */
#define ALT_L3_SEC_ACP_S_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_ACP_S register field. */
#define ALT_L3_SEC_ACP_S_RESET      0x0
/* Extracts the ALT_L3_SEC_ACP_S field value from a register. */
#define ALT_L3_SEC_ACP_S_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_ACP_S register field value suitable for setting the register. */
#define ALT_L3_SEC_ACP_S_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_ACP.
 */
struct ALT_L3_SEC_ACP_s
{
    uint32_t  s :  1;  /* MPU ACP Security */
    uint32_t    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_ACP. */
typedef volatile struct ALT_L3_SEC_ACP_s  ALT_L3_SEC_ACP_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_ACP register from the beginning of the component. */
#define ALT_L3_SEC_ACP_OFST        0x8c

/*
 * Register : ROM Peripheral Security - rom
 * 
 * Controls security settings for ROM peripheral.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description 
 * :-------|:-------|:------|:-------------
 *  [0]    | W      | 0x0   | ROM Security
 *  [31:1] | ???    | 0x0   | *UNDEFINED* 
 * 
 */
/*
 * Field : ROM Security - s
 * 
 * Controls whether secure or non-secure masters can access the ROM slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                         | Value | Description                                  
 * :-----------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_ROM_S_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                             |       | master.                                      
 *  ALT_L3_SEC_ROM_S_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                             |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_ROM_S
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_ROM_S_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_ROM_S
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_ROM_S_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_ROM_S register field. */
#define ALT_L3_SEC_ROM_S_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_ROM_S register field. */
#define ALT_L3_SEC_ROM_S_MSB        0
/* The width in bits of the ALT_L3_SEC_ROM_S register field. */
#define ALT_L3_SEC_ROM_S_WIDTH      1
/* The mask used to set the ALT_L3_SEC_ROM_S register field value. */
#define ALT_L3_SEC_ROM_S_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_ROM_S register field value. */
#define ALT_L3_SEC_ROM_S_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_ROM_S register field. */
#define ALT_L3_SEC_ROM_S_RESET      0x0
/* Extracts the ALT_L3_SEC_ROM_S field value from a register. */
#define ALT_L3_SEC_ROM_S_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_ROM_S register field value suitable for setting the register. */
#define ALT_L3_SEC_ROM_S_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_ROM.
 */
struct ALT_L3_SEC_ROM_s
{
    uint32_t  s :  1;  /* ROM Security */
    uint32_t    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_ROM. */
typedef volatile struct ALT_L3_SEC_ROM_s  ALT_L3_SEC_ROM_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_ROM register from the beginning of the component. */
#define ALT_L3_SEC_ROM_OFST        0x90

/*
 * Register : On-chip RAM Peripheral Security - ocram
 * 
 * Controls security settings for On-chip RAM peripheral.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description         
 * :-------|:-------|:------|:---------------------
 *  [0]    | W      | 0x0   | On-chip RAM Security
 *  [31:1] | ???    | 0x0   | *UNDEFINED*         
 * 
 */
/*
 * Field : On-chip RAM Security - s
 * 
 * Controls whether secure or non-secure masters can access the On-chip RAM slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                           | Value | Description                                  
 * :-------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_OCRAM_S_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                               |       | master.                                      
 *  ALT_L3_SEC_OCRAM_S_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                               |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_OCRAM_S
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_OCRAM_S_E_SECURE     0x0
/*
 * Enumerated value for register field ALT_L3_SEC_OCRAM_S
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_OCRAM_S_E_NONSECURE  0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_OCRAM_S register field. */
#define ALT_L3_SEC_OCRAM_S_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_OCRAM_S register field. */
#define ALT_L3_SEC_OCRAM_S_MSB        0
/* The width in bits of the ALT_L3_SEC_OCRAM_S register field. */
#define ALT_L3_SEC_OCRAM_S_WIDTH      1
/* The mask used to set the ALT_L3_SEC_OCRAM_S register field value. */
#define ALT_L3_SEC_OCRAM_S_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_OCRAM_S register field value. */
#define ALT_L3_SEC_OCRAM_S_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_OCRAM_S register field. */
#define ALT_L3_SEC_OCRAM_S_RESET      0x0
/* Extracts the ALT_L3_SEC_OCRAM_S field value from a register. */
#define ALT_L3_SEC_OCRAM_S_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_OCRAM_S register field value suitable for setting the register. */
#define ALT_L3_SEC_OCRAM_S_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_OCRAM.
 */
struct ALT_L3_SEC_OCRAM_s
{
    uint32_t  s :  1;  /* On-chip RAM Security */
    uint32_t    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_OCRAM. */
typedef volatile struct ALT_L3_SEC_OCRAM_s  ALT_L3_SEC_OCRAM_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_OCRAM register from the beginning of the component. */
#define ALT_L3_SEC_OCRAM_OFST        0x94

/*
 * Register : SDRAM Data Peripheral Security - sdrdata
 * 
 * Controls security settings for SDRAM Data peripheral.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description        
 * :-------|:-------|:------|:--------------------
 *  [0]    | W      | 0x0   | SDRAM Data Security
 *  [31:1] | ???    | 0x0   | *UNDEFINED*        
 * 
 */
/*
 * Field : SDRAM Data Security - s
 * 
 * Controls whether secure or non-secure masters can access the SDRAM Data slave.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                                  
 * :---------------------------------|:------|:----------------------------------------------
 *  ALT_L3_SEC_SDRDATA_S_E_SECURE    | 0x0   | The slave can only be accessed by a secure   
 * :                                 |       | master.                                      
 *  ALT_L3_SEC_SDRDATA_S_E_NONSECURE | 0x1   | The slave can only be accessed by a secure or
 * :                                 |       | non-secure masters.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_SEC_SDRDATA_S
 * 
 * The slave can only be accessed by a secure master.
 */
#define ALT_L3_SEC_SDRDATA_S_E_SECURE       0x0
/*
 * Enumerated value for register field ALT_L3_SEC_SDRDATA_S
 * 
 * The slave can only be accessed by a secure or non-secure masters.
 */
#define ALT_L3_SEC_SDRDATA_S_E_NONSECURE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_SEC_SDRDATA_S register field. */
#define ALT_L3_SEC_SDRDATA_S_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_SEC_SDRDATA_S register field. */
#define ALT_L3_SEC_SDRDATA_S_MSB        0
/* The width in bits of the ALT_L3_SEC_SDRDATA_S register field. */
#define ALT_L3_SEC_SDRDATA_S_WIDTH      1
/* The mask used to set the ALT_L3_SEC_SDRDATA_S register field value. */
#define ALT_L3_SEC_SDRDATA_S_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_SEC_SDRDATA_S register field value. */
#define ALT_L3_SEC_SDRDATA_S_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_SEC_SDRDATA_S register field. */
#define ALT_L3_SEC_SDRDATA_S_RESET      0x0
/* Extracts the ALT_L3_SEC_SDRDATA_S field value from a register. */
#define ALT_L3_SEC_SDRDATA_S_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_SEC_SDRDATA_S register field value suitable for setting the register. */
#define ALT_L3_SEC_SDRDATA_S_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_SEC_SDRDATA.
 */
struct ALT_L3_SEC_SDRDATA_s
{
    uint32_t  s :  1;  /* SDRAM Data Security */
    uint32_t    : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_SEC_SDRDATA. */
typedef volatile struct ALT_L3_SEC_SDRDATA_s  ALT_L3_SEC_SDRDATA_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_SEC_SDRDATA register from the beginning of the component. */
#define ALT_L3_SEC_SDRDATA_OFST        0x98

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_L3_SECGRP.
 */
struct ALT_L3_SECGRP_s
{
    volatile ALT_L3_SEC_L4MAIN_t       l4main;              /* ALT_L3_SEC_L4MAIN */
    volatile ALT_L3_SEC_L4SP_t         l4sp;                /* ALT_L3_SEC_L4SP */
    volatile ALT_L3_SEC_L4MP_t         l4mp;                /* ALT_L3_SEC_L4MP */
    volatile ALT_L3_SEC_L4OSC1_t       l4osc1;              /* ALT_L3_SEC_L4OSC1 */
    volatile ALT_L3_SEC_L4SPIM_t       l4spim;              /* ALT_L3_SEC_L4SPIM */
    volatile ALT_L3_SEC_STM_t          stm;                 /* ALT_L3_SEC_STM */
    volatile ALT_L3_SEC_LWH2F_t        lwhps2fpgaregs;      /* ALT_L3_SEC_LWH2F */
    volatile uint32_t                  _pad_0x1c_0x1f;      /* *UNDEFINED* */
    volatile ALT_L3_SEC_USB1_t         usb1;                /* ALT_L3_SEC_USB1 */
    volatile ALT_L3_SEC_NANDDATA_t     nanddata;            /* ALT_L3_SEC_NANDDATA */
    volatile uint32_t                  _pad_0x28_0x77[20];  /* *UNDEFINED* */
    volatile ALT_L3_SEC_USB0_t         usb0;                /* ALT_L3_SEC_USB0 */
    volatile ALT_L3_SEC_NAND_t         nandregs;            /* ALT_L3_SEC_NAND */
    volatile ALT_L3_SEC_QSPIDATA_t     qspidata;            /* ALT_L3_SEC_QSPIDATA */
    volatile ALT_L3_SEC_FPGAMGRDATA_t  fpgamgrdata;         /* ALT_L3_SEC_FPGAMGRDATA */
    volatile ALT_L3_SEC_H2F_t          hps2fpgaregs;        /* ALT_L3_SEC_H2F */
    volatile ALT_L3_SEC_ACP_t          acp;                 /* ALT_L3_SEC_ACP */
    volatile ALT_L3_SEC_ROM_t          rom;                 /* ALT_L3_SEC_ROM */
    volatile ALT_L3_SEC_OCRAM_t        ocram;               /* ALT_L3_SEC_OCRAM */
    volatile ALT_L3_SEC_SDRDATA_t      sdrdata;             /* ALT_L3_SEC_SDRDATA */
};

/* The typedef declaration for register group ALT_L3_SECGRP. */
typedef volatile struct ALT_L3_SECGRP_s  ALT_L3_SECGRP_t;
/* The struct declaration for the raw register contents of register group ALT_L3_SECGRP. */
struct ALT_L3_SECGRP_raw_s
{
    volatile uint32_t  l4main;              /* ALT_L3_SEC_L4MAIN */
    volatile uint32_t  l4sp;                /* ALT_L3_SEC_L4SP */
    volatile uint32_t  l4mp;                /* ALT_L3_SEC_L4MP */
    volatile uint32_t  l4osc1;              /* ALT_L3_SEC_L4OSC1 */
    volatile uint32_t  l4spim;              /* ALT_L3_SEC_L4SPIM */
    volatile uint32_t  stm;                 /* ALT_L3_SEC_STM */
    volatile uint32_t  lwhps2fpgaregs;      /* ALT_L3_SEC_LWH2F */
    volatile uint32_t  _pad_0x1c_0x1f;      /* *UNDEFINED* */
    volatile uint32_t  usb1;                /* ALT_L3_SEC_USB1 */
    volatile uint32_t  nanddata;            /* ALT_L3_SEC_NANDDATA */
    volatile uint32_t  _pad_0x28_0x77[20];  /* *UNDEFINED* */
    volatile uint32_t  usb0;                /* ALT_L3_SEC_USB0 */
    volatile uint32_t  nandregs;            /* ALT_L3_SEC_NAND */
    volatile uint32_t  qspidata;            /* ALT_L3_SEC_QSPIDATA */
    volatile uint32_t  fpgamgrdata;         /* ALT_L3_SEC_FPGAMGRDATA */
    volatile uint32_t  hps2fpgaregs;        /* ALT_L3_SEC_H2F */
    volatile uint32_t  acp;                 /* ALT_L3_SEC_ACP */
    volatile uint32_t  rom;                 /* ALT_L3_SEC_ROM */
    volatile uint32_t  ocram;               /* ALT_L3_SEC_OCRAM */
    volatile uint32_t  sdrdata;             /* ALT_L3_SEC_SDRDATA */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_SECGRP. */
typedef volatile struct ALT_L3_SECGRP_raw_s  ALT_L3_SECGRP_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : ID Register Group - ALT_L3_IDGRP
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
/* The Least Significant Bit (LSB) position of the ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4 register field. */
#define ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4 register field. */
#define ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4_MSB        7
/* The width in bits of the ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4 register field. */
#define ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4_WIDTH      8
/* The mask used to set the ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4 register field value. */
#define ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4_SET_MSK    0x000000ff
/* The mask used to clear the ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4 register field value. */
#define ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4_CLR_MSK    0xffffff00
/* The reset value of the ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4 register field. */
#define ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4_RESET      0x4
/* Extracts the ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4 field value from a register. */
#define ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4 register field value suitable for setting the register. */
#define ALT_L3_ID_PERIPH_ID_4_PERIPH_ID_4_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_ID_PERIPH_ID_4.
 */
struct ALT_L3_ID_PERIPH_ID_4_s
{
    const uint32_t  periph_id_4 :  8;  /* Peripheral ID4 */
    uint32_t                    : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_ID_PERIPH_ID_4. */
typedef volatile struct ALT_L3_ID_PERIPH_ID_4_s  ALT_L3_ID_PERIPH_ID_4_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_ID_PERIPH_ID_4 register from the beginning of the component. */
#define ALT_L3_ID_PERIPH_ID_4_OFST        0xfd0

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
/* The Least Significant Bit (LSB) position of the ALT_L3_ID_PERIPH_ID_0_PN7TO0 register field. */
#define ALT_L3_ID_PERIPH_ID_0_PN7TO0_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_ID_PERIPH_ID_0_PN7TO0 register field. */
#define ALT_L3_ID_PERIPH_ID_0_PN7TO0_MSB        7
/* The width in bits of the ALT_L3_ID_PERIPH_ID_0_PN7TO0 register field. */
#define ALT_L3_ID_PERIPH_ID_0_PN7TO0_WIDTH      8
/* The mask used to set the ALT_L3_ID_PERIPH_ID_0_PN7TO0 register field value. */
#define ALT_L3_ID_PERIPH_ID_0_PN7TO0_SET_MSK    0x000000ff
/* The mask used to clear the ALT_L3_ID_PERIPH_ID_0_PN7TO0 register field value. */
#define ALT_L3_ID_PERIPH_ID_0_PN7TO0_CLR_MSK    0xffffff00
/* The reset value of the ALT_L3_ID_PERIPH_ID_0_PN7TO0 register field. */
#define ALT_L3_ID_PERIPH_ID_0_PN7TO0_RESET      0x1
/* Extracts the ALT_L3_ID_PERIPH_ID_0_PN7TO0 field value from a register. */
#define ALT_L3_ID_PERIPH_ID_0_PN7TO0_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_L3_ID_PERIPH_ID_0_PN7TO0 register field value suitable for setting the register. */
#define ALT_L3_ID_PERIPH_ID_0_PN7TO0_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_ID_PERIPH_ID_0.
 */
struct ALT_L3_ID_PERIPH_ID_0_s
{
    const uint32_t  pn7to0 :  8;  /* Part Number [7:0] */
    uint32_t               : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_ID_PERIPH_ID_0. */
typedef volatile struct ALT_L3_ID_PERIPH_ID_0_s  ALT_L3_ID_PERIPH_ID_0_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_ID_PERIPH_ID_0 register from the beginning of the component. */
#define ALT_L3_ID_PERIPH_ID_0_OFST        0xfe0

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
/* The Least Significant Bit (LSB) position of the ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 register field. */
#define ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 register field. */
#define ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_MSB        7
/* The width in bits of the ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 register field. */
#define ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_WIDTH      8
/* The mask used to set the ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 register field value. */
#define ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_SET_MSK    0x000000ff
/* The mask used to clear the ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 register field value. */
#define ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_CLR_MSK    0xffffff00
/* The reset value of the ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 register field. */
#define ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_RESET      0xb3
/* Extracts the ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 field value from a register. */
#define ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8 register field value suitable for setting the register. */
#define ALT_L3_ID_PERIPH_ID_1_JEP3TO0_PN11TO8_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_ID_PERIPH_ID_1.
 */
struct ALT_L3_ID_PERIPH_ID_1_s
{
    const uint32_t  jep3to0_pn11to8 :  8;  /* JEP106[3:0], Part Number [11:8] */
    uint32_t                        : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_ID_PERIPH_ID_1. */
typedef volatile struct ALT_L3_ID_PERIPH_ID_1_s  ALT_L3_ID_PERIPH_ID_1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_ID_PERIPH_ID_1 register from the beginning of the component. */
#define ALT_L3_ID_PERIPH_ID_1_OFST        0xfe4

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
/* The Least Significant Bit (LSB) position of the ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 register field. */
#define ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 register field. */
#define ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_MSB        7
/* The width in bits of the ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 register field. */
#define ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_WIDTH      8
/* The mask used to set the ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 register field value. */
#define ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_SET_MSK    0x000000ff
/* The mask used to clear the ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 register field value. */
#define ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_CLR_MSK    0xffffff00
/* The reset value of the ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 register field. */
#define ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_RESET      0x6b
/* Extracts the ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 field value from a register. */
#define ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4 register field value suitable for setting the register. */
#define ALT_L3_ID_PERIPH_ID_2_REV_JEPCODE_JEP6TO4_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_ID_PERIPH_ID_2.
 */
struct ALT_L3_ID_PERIPH_ID_2_s
{
    const uint32_t  rev_jepcode_jep6to4 :  8;  /* Revision, JEP106 code flag, JEP106[6:4] */
    uint32_t                            : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_ID_PERIPH_ID_2. */
typedef volatile struct ALT_L3_ID_PERIPH_ID_2_s  ALT_L3_ID_PERIPH_ID_2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_ID_PERIPH_ID_2 register from the beginning of the component. */
#define ALT_L3_ID_PERIPH_ID_2_OFST        0xfe8

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
/* The Least Significant Bit (LSB) position of the ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM register field. */
#define ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM register field. */
#define ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM_MSB        3
/* The width in bits of the ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM register field. */
#define ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM_WIDTH      4
/* The mask used to set the ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM register field value. */
#define ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM_SET_MSK    0x0000000f
/* The mask used to clear the ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM register field value. */
#define ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM_CLR_MSK    0xfffffff0
/* The reset value of the ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM register field. */
#define ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM_RESET      0x0
/* Extracts the ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM field value from a register. */
#define ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM register field value suitable for setting the register. */
#define ALT_L3_ID_PERIPH_ID_3_CUST_MOD_NUM_SET(value) (((value) << 0) & 0x0000000f)

/*
 * Field : Revision - rev_and
 * 
 * Revision
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_L3_ID_PERIPH_ID_3_REV_AND register field. */
#define ALT_L3_ID_PERIPH_ID_3_REV_AND_LSB        4
/* The Most Significant Bit (MSB) position of the ALT_L3_ID_PERIPH_ID_3_REV_AND register field. */
#define ALT_L3_ID_PERIPH_ID_3_REV_AND_MSB        7
/* The width in bits of the ALT_L3_ID_PERIPH_ID_3_REV_AND register field. */
#define ALT_L3_ID_PERIPH_ID_3_REV_AND_WIDTH      4
/* The mask used to set the ALT_L3_ID_PERIPH_ID_3_REV_AND register field value. */
#define ALT_L3_ID_PERIPH_ID_3_REV_AND_SET_MSK    0x000000f0
/* The mask used to clear the ALT_L3_ID_PERIPH_ID_3_REV_AND register field value. */
#define ALT_L3_ID_PERIPH_ID_3_REV_AND_CLR_MSK    0xffffff0f
/* The reset value of the ALT_L3_ID_PERIPH_ID_3_REV_AND register field. */
#define ALT_L3_ID_PERIPH_ID_3_REV_AND_RESET      0x0
/* Extracts the ALT_L3_ID_PERIPH_ID_3_REV_AND field value from a register. */
#define ALT_L3_ID_PERIPH_ID_3_REV_AND_GET(value) (((value) & 0x000000f0) >> 4)
/* Produces a ALT_L3_ID_PERIPH_ID_3_REV_AND register field value suitable for setting the register. */
#define ALT_L3_ID_PERIPH_ID_3_REV_AND_SET(value) (((value) << 4) & 0x000000f0)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_ID_PERIPH_ID_3.
 */
struct ALT_L3_ID_PERIPH_ID_3_s
{
    const uint32_t  cust_mod_num :  4;  /* Customer Model Number */
    const uint32_t  rev_and      :  4;  /* Revision */
    uint32_t                     : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_ID_PERIPH_ID_3. */
typedef volatile struct ALT_L3_ID_PERIPH_ID_3_s  ALT_L3_ID_PERIPH_ID_3_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_ID_PERIPH_ID_3 register from the beginning of the component. */
#define ALT_L3_ID_PERIPH_ID_3_OFST        0xfec

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
/* The Least Significant Bit (LSB) position of the ALT_L3_ID_COMP_ID_0_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_0_PREAMBLE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_ID_COMP_ID_0_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_0_PREAMBLE_MSB        7
/* The width in bits of the ALT_L3_ID_COMP_ID_0_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_0_PREAMBLE_WIDTH      8
/* The mask used to set the ALT_L3_ID_COMP_ID_0_PREAMBLE register field value. */
#define ALT_L3_ID_COMP_ID_0_PREAMBLE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_L3_ID_COMP_ID_0_PREAMBLE register field value. */
#define ALT_L3_ID_COMP_ID_0_PREAMBLE_CLR_MSK    0xffffff00
/* The reset value of the ALT_L3_ID_COMP_ID_0_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_0_PREAMBLE_RESET      0xd
/* Extracts the ALT_L3_ID_COMP_ID_0_PREAMBLE field value from a register. */
#define ALT_L3_ID_COMP_ID_0_PREAMBLE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_L3_ID_COMP_ID_0_PREAMBLE register field value suitable for setting the register. */
#define ALT_L3_ID_COMP_ID_0_PREAMBLE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_ID_COMP_ID_0.
 */
struct ALT_L3_ID_COMP_ID_0_s
{
    const uint32_t  preamble :  8;  /* Preamble */
    uint32_t                 : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_ID_COMP_ID_0. */
typedef volatile struct ALT_L3_ID_COMP_ID_0_s  ALT_L3_ID_COMP_ID_0_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_ID_COMP_ID_0 register from the beginning of the component. */
#define ALT_L3_ID_COMP_ID_0_OFST        0xff0

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
/* The Least Significant Bit (LSB) position of the ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_MSB        7
/* The width in bits of the ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_WIDTH      8
/* The mask used to set the ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE register field value. */
#define ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE register field value. */
#define ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_CLR_MSK    0xffffff00
/* The reset value of the ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_RESET      0xf0
/* Extracts the ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE field value from a register. */
#define ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE register field value suitable for setting the register. */
#define ALT_L3_ID_COMP_ID_1_GENIPCOMPCLS_PREAMBLE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_ID_COMP_ID_1.
 */
struct ALT_L3_ID_COMP_ID_1_s
{
    const uint32_t  genipcompcls_preamble :  8;  /* Generic IP component class, Preamble */
    uint32_t                              : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_ID_COMP_ID_1. */
typedef volatile struct ALT_L3_ID_COMP_ID_1_s  ALT_L3_ID_COMP_ID_1_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_ID_COMP_ID_1 register from the beginning of the component. */
#define ALT_L3_ID_COMP_ID_1_OFST        0xff4

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
/* The Least Significant Bit (LSB) position of the ALT_L3_ID_COMP_ID_2_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_2_PREAMBLE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_ID_COMP_ID_2_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_2_PREAMBLE_MSB        7
/* The width in bits of the ALT_L3_ID_COMP_ID_2_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_2_PREAMBLE_WIDTH      8
/* The mask used to set the ALT_L3_ID_COMP_ID_2_PREAMBLE register field value. */
#define ALT_L3_ID_COMP_ID_2_PREAMBLE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_L3_ID_COMP_ID_2_PREAMBLE register field value. */
#define ALT_L3_ID_COMP_ID_2_PREAMBLE_CLR_MSK    0xffffff00
/* The reset value of the ALT_L3_ID_COMP_ID_2_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_2_PREAMBLE_RESET      0x5
/* Extracts the ALT_L3_ID_COMP_ID_2_PREAMBLE field value from a register. */
#define ALT_L3_ID_COMP_ID_2_PREAMBLE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_L3_ID_COMP_ID_2_PREAMBLE register field value suitable for setting the register. */
#define ALT_L3_ID_COMP_ID_2_PREAMBLE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_ID_COMP_ID_2.
 */
struct ALT_L3_ID_COMP_ID_2_s
{
    const uint32_t  preamble :  8;  /* Preamble */
    uint32_t                 : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_ID_COMP_ID_2. */
typedef volatile struct ALT_L3_ID_COMP_ID_2_s  ALT_L3_ID_COMP_ID_2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_ID_COMP_ID_2 register from the beginning of the component. */
#define ALT_L3_ID_COMP_ID_2_OFST        0xff8

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
/* The Least Significant Bit (LSB) position of the ALT_L3_ID_COMP_ID_3_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_3_PREAMBLE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_ID_COMP_ID_3_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_3_PREAMBLE_MSB        7
/* The width in bits of the ALT_L3_ID_COMP_ID_3_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_3_PREAMBLE_WIDTH      8
/* The mask used to set the ALT_L3_ID_COMP_ID_3_PREAMBLE register field value. */
#define ALT_L3_ID_COMP_ID_3_PREAMBLE_SET_MSK    0x000000ff
/* The mask used to clear the ALT_L3_ID_COMP_ID_3_PREAMBLE register field value. */
#define ALT_L3_ID_COMP_ID_3_PREAMBLE_CLR_MSK    0xffffff00
/* The reset value of the ALT_L3_ID_COMP_ID_3_PREAMBLE register field. */
#define ALT_L3_ID_COMP_ID_3_PREAMBLE_RESET      0xb1
/* Extracts the ALT_L3_ID_COMP_ID_3_PREAMBLE field value from a register. */
#define ALT_L3_ID_COMP_ID_3_PREAMBLE_GET(value) (((value) & 0x000000ff) >> 0)
/* Produces a ALT_L3_ID_COMP_ID_3_PREAMBLE register field value suitable for setting the register. */
#define ALT_L3_ID_COMP_ID_3_PREAMBLE_SET(value) (((value) << 0) & 0x000000ff)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_ID_COMP_ID_3.
 */
struct ALT_L3_ID_COMP_ID_3_s
{
    const uint32_t  preamble :  8;  /* Preamble */
    uint32_t                 : 24;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_ID_COMP_ID_3. */
typedef volatile struct ALT_L3_ID_COMP_ID_3_s  ALT_L3_ID_COMP_ID_3_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_ID_COMP_ID_3 register from the beginning of the component. */
#define ALT_L3_ID_COMP_ID_3_OFST        0xffc

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_L3_IDGRP.
 */
struct ALT_L3_IDGRP_s
{
    volatile uint32_t                 _pad_0x0_0xfcf[1012];  /* *UNDEFINED* */
    volatile ALT_L3_ID_PERIPH_ID_4_t  periph_id_4;           /* ALT_L3_ID_PERIPH_ID_4 */
    volatile uint32_t                 _pad_0xfd4_0xfdf[3];   /* *UNDEFINED* */
    volatile ALT_L3_ID_PERIPH_ID_0_t  periph_id_0;           /* ALT_L3_ID_PERIPH_ID_0 */
    volatile ALT_L3_ID_PERIPH_ID_1_t  periph_id_1;           /* ALT_L3_ID_PERIPH_ID_1 */
    volatile ALT_L3_ID_PERIPH_ID_2_t  periph_id_2;           /* ALT_L3_ID_PERIPH_ID_2 */
    volatile ALT_L3_ID_PERIPH_ID_3_t  periph_id_3;           /* ALT_L3_ID_PERIPH_ID_3 */
    volatile ALT_L3_ID_COMP_ID_0_t    comp_id_0;             /* ALT_L3_ID_COMP_ID_0 */
    volatile ALT_L3_ID_COMP_ID_1_t    comp_id_1;             /* ALT_L3_ID_COMP_ID_1 */
    volatile ALT_L3_ID_COMP_ID_2_t    comp_id_2;             /* ALT_L3_ID_COMP_ID_2 */
    volatile ALT_L3_ID_COMP_ID_3_t    comp_id_3;             /* ALT_L3_ID_COMP_ID_3 */
};

/* The typedef declaration for register group ALT_L3_IDGRP. */
typedef volatile struct ALT_L3_IDGRP_s  ALT_L3_IDGRP_t;
/* The struct declaration for the raw register contents of register group ALT_L3_IDGRP. */
struct ALT_L3_IDGRP_raw_s
{
    volatile uint32_t  _pad_0x0_0xfcf[1012];  /* *UNDEFINED* */
    volatile uint32_t  periph_id_4;           /* ALT_L3_ID_PERIPH_ID_4 */
    volatile uint32_t  _pad_0xfd4_0xfdf[3];   /* *UNDEFINED* */
    volatile uint32_t  periph_id_0;           /* ALT_L3_ID_PERIPH_ID_0 */
    volatile uint32_t  periph_id_1;           /* ALT_L3_ID_PERIPH_ID_1 */
    volatile uint32_t  periph_id_2;           /* ALT_L3_ID_PERIPH_ID_2 */
    volatile uint32_t  periph_id_3;           /* ALT_L3_ID_PERIPH_ID_3 */
    volatile uint32_t  comp_id_0;             /* ALT_L3_ID_COMP_ID_0 */
    volatile uint32_t  comp_id_1;             /* ALT_L3_ID_COMP_ID_1 */
    volatile uint32_t  comp_id_2;             /* ALT_L3_ID_COMP_ID_2 */
    volatile uint32_t  comp_id_3;             /* ALT_L3_ID_COMP_ID_3 */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_IDGRP. */
typedef volatile struct ALT_L3_IDGRP_raw_s  ALT_L3_IDGRP_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : Master Register Group - ALT_L3_MSTGRP
 * Master Register Group
 * 
 * Registers associated with master interfaces in the L3 Interconnect. Note that a
 * master in the L3 Interconnect connects to a slave in a module.
 * 
 */
/*
 * Register Group : L4 MAIN - ALT_L3_MST_L4MAIN
 * L4 MAIN
 * 
 * Registers associated with the L4 MAIN master. This master is used to access the
 * APB slaves on the L4 MAIN bus.
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
 * :-------|:-------|:------|:------------------------
 *  [0]    | RW     | 0x0   | ALT_L3_FN_MOD_BM_ISS_RD
 *  [1]    | RW     | 0x0   | ALT_L3_FN_MOD_BM_ISS_WR
 *  [31:2] | ???    | 0x0   | *UNDEFINED*            
 * 
 */
/*
 * Field : rd
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                               
 * :---------------------------------|:------|:-------------------------------------------
 *  ALT_L3_FN_MOD_BM_ISS_RD_E_MULT   | 0x0   | Multiple outstanding read transactions    
 *  ALT_L3_FN_MOD_BM_ISS_RD_E_SINGLE | 0x1   | Only a single outstanding read transaction
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_FN_MOD_BM_ISS_RD
 * 
 * Multiple outstanding read transactions
 */
#define ALT_L3_FN_MOD_BM_ISS_RD_E_MULT      0x0
/*
 * Enumerated value for register field ALT_L3_FN_MOD_BM_ISS_RD
 * 
 * Only a single outstanding read transaction
 */
#define ALT_L3_FN_MOD_BM_ISS_RD_E_SINGLE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_FN_MOD_BM_ISS_RD register field. */
#define ALT_L3_FN_MOD_BM_ISS_RD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_FN_MOD_BM_ISS_RD register field. */
#define ALT_L3_FN_MOD_BM_ISS_RD_MSB        0
/* The width in bits of the ALT_L3_FN_MOD_BM_ISS_RD register field. */
#define ALT_L3_FN_MOD_BM_ISS_RD_WIDTH      1
/* The mask used to set the ALT_L3_FN_MOD_BM_ISS_RD register field value. */
#define ALT_L3_FN_MOD_BM_ISS_RD_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_FN_MOD_BM_ISS_RD register field value. */
#define ALT_L3_FN_MOD_BM_ISS_RD_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_FN_MOD_BM_ISS_RD register field. */
#define ALT_L3_FN_MOD_BM_ISS_RD_RESET      0x0
/* Extracts the ALT_L3_FN_MOD_BM_ISS_RD field value from a register. */
#define ALT_L3_FN_MOD_BM_ISS_RD_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_FN_MOD_BM_ISS_RD register field value suitable for setting the register. */
#define ALT_L3_FN_MOD_BM_ISS_RD_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : wr
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                                
 * :---------------------------------|:------|:--------------------------------------------
 *  ALT_L3_FN_MOD_BM_ISS_WR_E_MULT   | 0x0   | Multiple outstanding write transactions    
 *  ALT_L3_FN_MOD_BM_ISS_WR_E_SINGLE | 0x1   | Only a single outstanding write transaction
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_FN_MOD_BM_ISS_WR
 * 
 * Multiple outstanding write transactions
 */
#define ALT_L3_FN_MOD_BM_ISS_WR_E_MULT      0x0
/*
 * Enumerated value for register field ALT_L3_FN_MOD_BM_ISS_WR
 * 
 * Only a single outstanding write transaction
 */
#define ALT_L3_FN_MOD_BM_ISS_WR_E_SINGLE    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_FN_MOD_BM_ISS_WR register field. */
#define ALT_L3_FN_MOD_BM_ISS_WR_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_L3_FN_MOD_BM_ISS_WR register field. */
#define ALT_L3_FN_MOD_BM_ISS_WR_MSB        1
/* The width in bits of the ALT_L3_FN_MOD_BM_ISS_WR register field. */
#define ALT_L3_FN_MOD_BM_ISS_WR_WIDTH      1
/* The mask used to set the ALT_L3_FN_MOD_BM_ISS_WR register field value. */
#define ALT_L3_FN_MOD_BM_ISS_WR_SET_MSK    0x00000002
/* The mask used to clear the ALT_L3_FN_MOD_BM_ISS_WR register field value. */
#define ALT_L3_FN_MOD_BM_ISS_WR_CLR_MSK    0xfffffffd
/* The reset value of the ALT_L3_FN_MOD_BM_ISS_WR register field. */
#define ALT_L3_FN_MOD_BM_ISS_WR_RESET      0x0
/* Extracts the ALT_L3_FN_MOD_BM_ISS_WR field value from a register. */
#define ALT_L3_FN_MOD_BM_ISS_WR_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_L3_FN_MOD_BM_ISS_WR register field value suitable for setting the register. */
#define ALT_L3_FN_MOD_BM_ISS_WR_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_FN_MOD_BM_ISS.
 */
struct ALT_L3_FN_MOD_BM_ISS_s
{
    uint32_t  rd :  1;  /* ALT_L3_FN_MOD_BM_ISS_RD */
    uint32_t  wr :  1;  /* ALT_L3_FN_MOD_BM_ISS_WR */
    uint32_t     : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_FN_MOD_BM_ISS. */
typedef volatile struct ALT_L3_FN_MOD_BM_ISS_s  ALT_L3_FN_MOD_BM_ISS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_FN_MOD_BM_ISS register from the beginning of the component. */
#define ALT_L3_FN_MOD_BM_ISS_OFST        0x8
/* The address of the ALT_L3_FN_MOD_BM_ISS register. */
#define ALT_L3_FN_MOD_BM_ISS_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L3_FN_MOD_BM_ISS_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_L3_MST_L4MAIN.
 */
struct ALT_L3_MST_L4MAIN_s
{
    volatile uint32_t                _pad_0x0_0x7[2];  /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;    /* ALT_L3_FN_MOD_BM_ISS */
};

/* The typedef declaration for register group ALT_L3_MST_L4MAIN. */
typedef volatile struct ALT_L3_MST_L4MAIN_s  ALT_L3_MST_L4MAIN_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_L4MAIN. */
struct ALT_L3_MST_L4MAIN_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;    /* ALT_L3_FN_MOD_BM_ISS */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_L4MAIN. */
typedef volatile struct ALT_L3_MST_L4MAIN_raw_s  ALT_L3_MST_L4MAIN_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : L4 SP - ALT_L3_MST_L4SP
 * L4 SP
 * 
 * Registers associated with the L4 SP master. This master is used to access the
 * APB slaves on the L4 SP bus.
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
 * The struct declaration for register group ALT_L3_MST_L4SP.
 */
struct ALT_L3_MST_L4SP_s
{
    volatile uint32_t                _pad_0x0_0x7[2];  /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;    /* ALT_L3_FN_MOD_BM_ISS */
};

/* The typedef declaration for register group ALT_L3_MST_L4SP. */
typedef volatile struct ALT_L3_MST_L4SP_s  ALT_L3_MST_L4SP_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_L4SP. */
struct ALT_L3_MST_L4SP_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;    /* ALT_L3_FN_MOD_BM_ISS */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_L4SP. */
typedef volatile struct ALT_L3_MST_L4SP_raw_s  ALT_L3_MST_L4SP_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : L4 MP - ALT_L3_MST_L4MP
 * L4 MP
 * 
 * Registers associated with the L4 MP master. This master is used to access the
 * APB slaves on the L4 MP bus.
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
 * The struct declaration for register group ALT_L3_MST_L4MP.
 */
struct ALT_L3_MST_L4MP_s
{
    volatile uint32_t                _pad_0x0_0x7[2];  /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;    /* ALT_L3_FN_MOD_BM_ISS */
};

/* The typedef declaration for register group ALT_L3_MST_L4MP. */
typedef volatile struct ALT_L3_MST_L4MP_s  ALT_L3_MST_L4MP_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_L4MP. */
struct ALT_L3_MST_L4MP_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;    /* ALT_L3_FN_MOD_BM_ISS */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_L4MP. */
typedef volatile struct ALT_L3_MST_L4MP_raw_s  ALT_L3_MST_L4MP_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : L4 OSC1 - ALT_L3_MST_L4OSC1
 * L4 OSC1
 * 
 * Registers associated with the L4 OSC1 master. This master is used to access the
 * APB slaves on the L4 OSC1 bus.
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
 * The struct declaration for register group ALT_L3_MST_L4OSC1.
 */
struct ALT_L3_MST_L4OSC1_s
{
    volatile uint32_t                _pad_0x0_0x7[2];  /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;    /* ALT_L3_FN_MOD_BM_ISS */
};

/* The typedef declaration for register group ALT_L3_MST_L4OSC1. */
typedef volatile struct ALT_L3_MST_L4OSC1_s  ALT_L3_MST_L4OSC1_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_L4OSC1. */
struct ALT_L3_MST_L4OSC1_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;    /* ALT_L3_FN_MOD_BM_ISS */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_L4OSC1. */
typedef volatile struct ALT_L3_MST_L4OSC1_raw_s  ALT_L3_MST_L4OSC1_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : L4 SPIM - ALT_L3_MST_L4SPIM
 * L4 SPIM
 * 
 * Registers associated with the L4 SPIM master. This master is used to access the
 * APB slaves on the L4 SPIM bus.
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
 * The struct declaration for register group ALT_L3_MST_L4SPIM.
 */
struct ALT_L3_MST_L4SPIM_s
{
    volatile uint32_t                _pad_0x0_0x7[2];  /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;    /* ALT_L3_FN_MOD_BM_ISS */
};

/* The typedef declaration for register group ALT_L3_MST_L4SPIM. */
typedef volatile struct ALT_L3_MST_L4SPIM_s  ALT_L3_MST_L4SPIM_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_L4SPIM. */
struct ALT_L3_MST_L4SPIM_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;    /* ALT_L3_FN_MOD_BM_ISS */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_L4SPIM. */
typedef volatile struct ALT_L3_MST_L4SPIM_raw_s  ALT_L3_MST_L4SPIM_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : STM - ALT_L3_MST_STM
 * STM
 * 
 * Registers associated with the STM master. This master is used to access the STM
 * AXI slave.
 * 
 */
/*
 * Register : Issuing Functionality Modification Register - fn_mod
 * 
 * Sets the block issuing capability to multiple or single outstanding
 * transactions.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description     
 * :-------|:-------|:------|:-----------------
 *  [0]    | RW     | 0x0   | ALT_L3_FN_MOD_RD
 *  [1]    | RW     | 0x0   | ALT_L3_FN_MOD_WR
 *  [31:2] | ???    | 0x0   | *UNDEFINED*     
 * 
 */
/*
 * Field : rd
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description                               
 * :--------------------------|:------|:-------------------------------------------
 *  ALT_L3_FN_MOD_RD_E_MULT   | 0x0   | Multiple outstanding read transactions    
 *  ALT_L3_FN_MOD_RD_E_SINGLE | 0x1   | Only a single outstanding read transaction
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_FN_MOD_RD
 * 
 * Multiple outstanding read transactions
 */
#define ALT_L3_FN_MOD_RD_E_MULT     0x0
/*
 * Enumerated value for register field ALT_L3_FN_MOD_RD
 * 
 * Only a single outstanding read transaction
 */
#define ALT_L3_FN_MOD_RD_E_SINGLE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_FN_MOD_RD register field. */
#define ALT_L3_FN_MOD_RD_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_FN_MOD_RD register field. */
#define ALT_L3_FN_MOD_RD_MSB        0
/* The width in bits of the ALT_L3_FN_MOD_RD register field. */
#define ALT_L3_FN_MOD_RD_WIDTH      1
/* The mask used to set the ALT_L3_FN_MOD_RD register field value. */
#define ALT_L3_FN_MOD_RD_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_FN_MOD_RD register field value. */
#define ALT_L3_FN_MOD_RD_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_FN_MOD_RD register field. */
#define ALT_L3_FN_MOD_RD_RESET      0x0
/* Extracts the ALT_L3_FN_MOD_RD field value from a register. */
#define ALT_L3_FN_MOD_RD_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_FN_MOD_RD register field value suitable for setting the register. */
#define ALT_L3_FN_MOD_RD_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : wr
 * 
 * Field Enumeration Values:
 * 
 *  Enum                      | Value | Description                                
 * :--------------------------|:------|:--------------------------------------------
 *  ALT_L3_FN_MOD_WR_E_MULT   | 0x0   | Multiple outstanding write transactions    
 *  ALT_L3_FN_MOD_WR_E_SINGLE | 0x1   | Only a single outstanding write transaction
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_FN_MOD_WR
 * 
 * Multiple outstanding write transactions
 */
#define ALT_L3_FN_MOD_WR_E_MULT     0x0
/*
 * Enumerated value for register field ALT_L3_FN_MOD_WR
 * 
 * Only a single outstanding write transaction
 */
#define ALT_L3_FN_MOD_WR_E_SINGLE   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_FN_MOD_WR register field. */
#define ALT_L3_FN_MOD_WR_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_L3_FN_MOD_WR register field. */
#define ALT_L3_FN_MOD_WR_MSB        1
/* The width in bits of the ALT_L3_FN_MOD_WR register field. */
#define ALT_L3_FN_MOD_WR_WIDTH      1
/* The mask used to set the ALT_L3_FN_MOD_WR register field value. */
#define ALT_L3_FN_MOD_WR_SET_MSK    0x00000002
/* The mask used to clear the ALT_L3_FN_MOD_WR register field value. */
#define ALT_L3_FN_MOD_WR_CLR_MSK    0xfffffffd
/* The reset value of the ALT_L3_FN_MOD_WR register field. */
#define ALT_L3_FN_MOD_WR_RESET      0x0
/* Extracts the ALT_L3_FN_MOD_WR field value from a register. */
#define ALT_L3_FN_MOD_WR_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_L3_FN_MOD_WR register field value suitable for setting the register. */
#define ALT_L3_FN_MOD_WR_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_FN_MOD.
 */
struct ALT_L3_FN_MOD_s
{
    uint32_t  rd :  1;  /* ALT_L3_FN_MOD_RD */
    uint32_t  wr :  1;  /* ALT_L3_FN_MOD_WR */
    uint32_t     : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_FN_MOD. */
typedef volatile struct ALT_L3_FN_MOD_s  ALT_L3_FN_MOD_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_FN_MOD register from the beginning of the component. */
#define ALT_L3_FN_MOD_OFST        0x108
/* The address of the ALT_L3_FN_MOD register. */
#define ALT_L3_FN_MOD_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L3_FN_MOD_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_L3_MST_STM.
 */
struct ALT_L3_MST_STM_s
{
    volatile uint32_t                _pad_0x0_0x7[2];     /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;       /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t                _pad_0xc_0x107[63];  /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_t         fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_MST_STM. */
typedef volatile struct ALT_L3_MST_STM_s  ALT_L3_MST_STM_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_STM. */
struct ALT_L3_MST_STM_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];     /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;       /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x107[63];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_STM. */
typedef volatile struct ALT_L3_MST_STM_raw_s  ALT_L3_MST_STM_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : LWHPS2FPGA - ALT_L3_MST_LWH2F
 * LWHPS2FPGA
 * 
 * Registers associated with the LWHPS2FPGA AXI Bridge master. This master is used
 * to access the LWHPS2FPGA AXI Bridge slave. This slave is used to access the
 * registers for all 3 AXI bridges and to access slaves in the FPGA connected to
 * the LWHPS2FPGA AXI Bridge.
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
 * The struct declaration for register group ALT_L3_MST_LWH2F.
 */
struct ALT_L3_MST_LWH2F_s
{
    volatile uint32_t                _pad_0x0_0x7[2];     /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;       /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t                _pad_0xc_0x107[63];  /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_t         fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_MST_LWH2F. */
typedef volatile struct ALT_L3_MST_LWH2F_s  ALT_L3_MST_LWH2F_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_LWH2F. */
struct ALT_L3_MST_LWH2F_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];     /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;       /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x107[63];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_LWH2F. */
typedef volatile struct ALT_L3_MST_LWH2F_raw_s  ALT_L3_MST_LWH2F_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : USB1 - ALT_L3_MST_USB1
 * USB1
 * 
 * Registers associated with the USB1 master. This master is used to access the
 * registers in USB1.
 * 
 */
/*
 * Register : AHB Control Register - ahb_cntl
 * 
 * Sets the block issuing capability to one outstanding transaction.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description               
 * :-------|:-------|:------|:---------------------------
 *  [0]    | RW     | 0x0   | ALT_L3_AHB_CNTL_DECERR_EN 
 *  [1]    | RW     | 0x0   | ALT_L3_AHB_CNTL_FORCE_INCR
 *  [31:2] | ???    | 0x0   | *UNDEFINED*               
 * 
 */
/*
 * Field : decerr_en
 * 
 * Field Enumeration Values:
 * 
 *  Enum                            | Value | Description                                     
 * :--------------------------------|:------|:-------------------------------------------------
 *  ALT_L3_AHB_CNTL_DECERR_EN_E_DIS | 0x0   | No DECERR response.                             
 *  ALT_L3_AHB_CNTL_DECERR_EN_E_EN  | 0x1   | If the AHB protocol conversion function receives
 * :                                |       | an unaligned address or a write data beat       
 * :                                |       | without all the byte strobes set, creates a     
 * :                                |       | DECERR response.                                
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_AHB_CNTL_DECERR_EN
 * 
 * No DECERR response.
 */
#define ALT_L3_AHB_CNTL_DECERR_EN_E_DIS 0x0
/*
 * Enumerated value for register field ALT_L3_AHB_CNTL_DECERR_EN
 * 
 * If the AHB protocol conversion function receives an unaligned address or a write
 * data beat without all the byte strobes set, creates a DECERR response.
 */
#define ALT_L3_AHB_CNTL_DECERR_EN_E_EN  0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_AHB_CNTL_DECERR_EN register field. */
#define ALT_L3_AHB_CNTL_DECERR_EN_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_AHB_CNTL_DECERR_EN register field. */
#define ALT_L3_AHB_CNTL_DECERR_EN_MSB        0
/* The width in bits of the ALT_L3_AHB_CNTL_DECERR_EN register field. */
#define ALT_L3_AHB_CNTL_DECERR_EN_WIDTH      1
/* The mask used to set the ALT_L3_AHB_CNTL_DECERR_EN register field value. */
#define ALT_L3_AHB_CNTL_DECERR_EN_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_AHB_CNTL_DECERR_EN register field value. */
#define ALT_L3_AHB_CNTL_DECERR_EN_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_AHB_CNTL_DECERR_EN register field. */
#define ALT_L3_AHB_CNTL_DECERR_EN_RESET      0x0
/* Extracts the ALT_L3_AHB_CNTL_DECERR_EN field value from a register. */
#define ALT_L3_AHB_CNTL_DECERR_EN_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_AHB_CNTL_DECERR_EN register field value suitable for setting the register. */
#define ALT_L3_AHB_CNTL_DECERR_EN_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : force_incr
 * 
 * Field Enumeration Values:
 * 
 *  Enum                             | Value | Description                                     
 * :---------------------------------|:------|:-------------------------------------------------
 *  ALT_L3_AHB_CNTL_FORCE_INCR_E_DIS | 0x0   | Multiple outstanding write transactions         
 *  ALT_L3_AHB_CNTL_FORCE_INCR_E_EN  | 0x1   | If a beat is received that has no write data    
 * :                                 |       | strobes set, that write data beat is replaced   
 * :                                 |       | with an IDLE beat. Also, causes all transactions
 * :                                 |       | that are to be output to the AHB domain to be an
 * :                                 |       | undefined length INCR.                          
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_AHB_CNTL_FORCE_INCR
 * 
 * Multiple outstanding write transactions
 */
#define ALT_L3_AHB_CNTL_FORCE_INCR_E_DIS    0x0
/*
 * Enumerated value for register field ALT_L3_AHB_CNTL_FORCE_INCR
 * 
 * If a beat is received that has no write data strobes set, that write data beat
 * is replaced with an IDLE beat. Also, causes all transactions that are to be
 * output to the AHB domain to be an undefined length INCR.
 */
#define ALT_L3_AHB_CNTL_FORCE_INCR_E_EN     0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_AHB_CNTL_FORCE_INCR register field. */
#define ALT_L3_AHB_CNTL_FORCE_INCR_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_L3_AHB_CNTL_FORCE_INCR register field. */
#define ALT_L3_AHB_CNTL_FORCE_INCR_MSB        1
/* The width in bits of the ALT_L3_AHB_CNTL_FORCE_INCR register field. */
#define ALT_L3_AHB_CNTL_FORCE_INCR_WIDTH      1
/* The mask used to set the ALT_L3_AHB_CNTL_FORCE_INCR register field value. */
#define ALT_L3_AHB_CNTL_FORCE_INCR_SET_MSK    0x00000002
/* The mask used to clear the ALT_L3_AHB_CNTL_FORCE_INCR register field value. */
#define ALT_L3_AHB_CNTL_FORCE_INCR_CLR_MSK    0xfffffffd
/* The reset value of the ALT_L3_AHB_CNTL_FORCE_INCR register field. */
#define ALT_L3_AHB_CNTL_FORCE_INCR_RESET      0x0
/* Extracts the ALT_L3_AHB_CNTL_FORCE_INCR field value from a register. */
#define ALT_L3_AHB_CNTL_FORCE_INCR_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_L3_AHB_CNTL_FORCE_INCR register field value suitable for setting the register. */
#define ALT_L3_AHB_CNTL_FORCE_INCR_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_AHB_CNTL.
 */
struct ALT_L3_AHB_CNTL_s
{
    uint32_t  decerr_en  :  1;  /* ALT_L3_AHB_CNTL_DECERR_EN */
    uint32_t  force_incr :  1;  /* ALT_L3_AHB_CNTL_FORCE_INCR */
    uint32_t             : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_AHB_CNTL. */
typedef volatile struct ALT_L3_AHB_CNTL_s  ALT_L3_AHB_CNTL_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_AHB_CNTL register from the beginning of the component. */
#define ALT_L3_AHB_CNTL_OFST        0x44
/* The address of the ALT_L3_AHB_CNTL register. */
#define ALT_L3_AHB_CNTL_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L3_AHB_CNTL_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_L3_MST_USB1.
 */
struct ALT_L3_MST_USB1_s
{
    volatile uint32_t                _pad_0x0_0x7[2];    /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;      /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t                _pad_0xc_0x43[14];  /* *UNDEFINED* */
    volatile ALT_L3_AHB_CNTL_t       ahb_cntl;           /* ALT_L3_AHB_CNTL */
};

/* The typedef declaration for register group ALT_L3_MST_USB1. */
typedef volatile struct ALT_L3_MST_USB1_s  ALT_L3_MST_USB1_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_USB1. */
struct ALT_L3_MST_USB1_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];    /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;      /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x43[14];  /* *UNDEFINED* */
    volatile uint32_t  ahb_cntl;           /* ALT_L3_AHB_CNTL */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_USB1. */
typedef volatile struct ALT_L3_MST_USB1_raw_s  ALT_L3_MST_USB1_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : NANDDATA - ALT_L3_MST_NANDDATA
 * NANDDATA
 * 
 * Registers associated with the NANDDATA master. This master is used to access
 * data in the NAND flash controller.
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
 * The struct declaration for register group ALT_L3_MST_NANDDATA.
 */
struct ALT_L3_MST_NANDDATA_s
{
    volatile uint32_t                _pad_0x0_0x7[2];     /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;       /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t                _pad_0xc_0x107[63];  /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_t         fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_MST_NANDDATA. */
typedef volatile struct ALT_L3_MST_NANDDATA_s  ALT_L3_MST_NANDDATA_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_NANDDATA. */
struct ALT_L3_MST_NANDDATA_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];     /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;       /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x107[63];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_NANDDATA. */
typedef volatile struct ALT_L3_MST_NANDDATA_raw_s  ALT_L3_MST_NANDDATA_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : USB0 - ALT_L3_MST_USB0
 * USB0
 * 
 * Registers associated with the USB0 master. This master is used to access the
 * registers in USB0.
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
 * The struct declaration for register group ALT_L3_MST_USB0.
 */
struct ALT_L3_MST_USB0_s
{
    volatile uint32_t                _pad_0x0_0x7[2];    /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;      /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t                _pad_0xc_0x43[14];  /* *UNDEFINED* */
    volatile ALT_L3_AHB_CNTL_t       ahb_cntl;           /* ALT_L3_AHB_CNTL */
};

/* The typedef declaration for register group ALT_L3_MST_USB0. */
typedef volatile struct ALT_L3_MST_USB0_s  ALT_L3_MST_USB0_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_USB0. */
struct ALT_L3_MST_USB0_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];    /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;      /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x43[14];  /* *UNDEFINED* */
    volatile uint32_t  ahb_cntl;           /* ALT_L3_AHB_CNTL */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_USB0. */
typedef volatile struct ALT_L3_MST_USB0_raw_s  ALT_L3_MST_USB0_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : NANDREGS - ALT_L3_MST_NAND
 * NANDREGS
 * 
 * Registers associated with the NANDREGS master. This master is used to access the
 * registers in the NAND flash controller.
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
 * The struct declaration for register group ALT_L3_MST_NAND.
 */
struct ALT_L3_MST_NAND_s
{
    volatile uint32_t                _pad_0x0_0x7[2];     /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;       /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t                _pad_0xc_0x107[63];  /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_t         fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_MST_NAND. */
typedef volatile struct ALT_L3_MST_NAND_s  ALT_L3_MST_NAND_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_NAND. */
struct ALT_L3_MST_NAND_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];     /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;       /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x107[63];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_NAND. */
typedef volatile struct ALT_L3_MST_NAND_raw_s  ALT_L3_MST_NAND_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : QSPIDATA - ALT_L3_MST_QSPIDATA
 * QSPIDATA
 * 
 * Registers associated with the QSPIDATA master. This master is used to access
 * data in the QSPI flash controller.
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
 * The struct declaration for register group ALT_L3_MST_QSPIDATA.
 */
struct ALT_L3_MST_QSPIDATA_s
{
    volatile uint32_t                _pad_0x0_0x7[2];    /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;      /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t                _pad_0xc_0x43[14];  /* *UNDEFINED* */
    volatile ALT_L3_AHB_CNTL_t       ahb_cntl;           /* ALT_L3_AHB_CNTL */
};

/* The typedef declaration for register group ALT_L3_MST_QSPIDATA. */
typedef volatile struct ALT_L3_MST_QSPIDATA_s  ALT_L3_MST_QSPIDATA_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_QSPIDATA. */
struct ALT_L3_MST_QSPIDATA_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];    /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;      /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x43[14];  /* *UNDEFINED* */
    volatile uint32_t  ahb_cntl;           /* ALT_L3_AHB_CNTL */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_QSPIDATA. */
typedef volatile struct ALT_L3_MST_QSPIDATA_raw_s  ALT_L3_MST_QSPIDATA_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : FPGAMGRDATA - ALT_L3_MST_FPGAMGRDATA
 * FPGAMGRDATA
 * 
 * Registers associated with the FPGAMGRDATA master. This master is used to send
 * FPGA configuration image data to the FPGA Manager.
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
/* The Least Significant Bit (LSB) position of the ALT_L3_WR_TIDEMARK_LEVEL register field. */
#define ALT_L3_WR_TIDEMARK_LEVEL_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_WR_TIDEMARK_LEVEL register field. */
#define ALT_L3_WR_TIDEMARK_LEVEL_MSB        3
/* The width in bits of the ALT_L3_WR_TIDEMARK_LEVEL register field. */
#define ALT_L3_WR_TIDEMARK_LEVEL_WIDTH      4
/* The mask used to set the ALT_L3_WR_TIDEMARK_LEVEL register field value. */
#define ALT_L3_WR_TIDEMARK_LEVEL_SET_MSK    0x0000000f
/* The mask used to clear the ALT_L3_WR_TIDEMARK_LEVEL register field value. */
#define ALT_L3_WR_TIDEMARK_LEVEL_CLR_MSK    0xfffffff0
/* The reset value of the ALT_L3_WR_TIDEMARK_LEVEL register field. */
#define ALT_L3_WR_TIDEMARK_LEVEL_RESET      0x4
/* Extracts the ALT_L3_WR_TIDEMARK_LEVEL field value from a register. */
#define ALT_L3_WR_TIDEMARK_LEVEL_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_L3_WR_TIDEMARK_LEVEL register field value suitable for setting the register. */
#define ALT_L3_WR_TIDEMARK_LEVEL_SET(value) (((value) << 0) & 0x0000000f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_WR_TIDEMARK.
 */
struct ALT_L3_WR_TIDEMARK_s
{
    uint32_t  level :  4;  /* Level */
    uint32_t        : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_WR_TIDEMARK. */
typedef volatile struct ALT_L3_WR_TIDEMARK_s  ALT_L3_WR_TIDEMARK_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_WR_TIDEMARK register from the beginning of the component. */
#define ALT_L3_WR_TIDEMARK_OFST        0x40
/* The address of the ALT_L3_WR_TIDEMARK register. */
#define ALT_L3_WR_TIDEMARK_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L3_WR_TIDEMARK_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_L3_MST_FPGAMGRDATA.
 */
struct ALT_L3_MST_FPGAMGRDATA_s
{
    volatile uint32_t                _pad_0x0_0x7[2];      /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;        /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t                _pad_0xc_0x3f[13];    /* *UNDEFINED* */
    volatile ALT_L3_WR_TIDEMARK_t    wr_tidemark;          /* ALT_L3_WR_TIDEMARK */
    volatile uint32_t                _pad_0x44_0x107[49];  /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_t         fn_mod;               /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_MST_FPGAMGRDATA. */
typedef volatile struct ALT_L3_MST_FPGAMGRDATA_s  ALT_L3_MST_FPGAMGRDATA_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_FPGAMGRDATA. */
struct ALT_L3_MST_FPGAMGRDATA_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];      /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;        /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x3f[13];    /* *UNDEFINED* */
    volatile uint32_t  wr_tidemark;          /* ALT_L3_WR_TIDEMARK */
    volatile uint32_t  _pad_0x44_0x107[49];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod;               /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_FPGAMGRDATA. */
typedef volatile struct ALT_L3_MST_FPGAMGRDATA_raw_s  ALT_L3_MST_FPGAMGRDATA_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : HPS2FPGA - ALT_L3_MST_H2F
 * HPS2FPGA
 * 
 * Registers associated with the HPS2FPGA AXI Bridge master. This master is used to
 * access the HPS2FPGA AXI Bridge slave. This slave is used to access slaves in the
 * FPGA connected to the HPS2FPGA AXI Bridge.
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
 * The struct declaration for register group ALT_L3_MST_H2F.
 */
struct ALT_L3_MST_H2F_s
{
    volatile uint32_t                _pad_0x0_0x7[2];      /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;        /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t                _pad_0xc_0x3f[13];    /* *UNDEFINED* */
    volatile ALT_L3_WR_TIDEMARK_t    wr_tidemark;          /* ALT_L3_WR_TIDEMARK */
    volatile uint32_t                _pad_0x44_0x107[49];  /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_t         fn_mod;               /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_MST_H2F. */
typedef volatile struct ALT_L3_MST_H2F_s  ALT_L3_MST_H2F_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_H2F. */
struct ALT_L3_MST_H2F_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];      /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;        /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x3f[13];    /* *UNDEFINED* */
    volatile uint32_t  wr_tidemark;          /* ALT_L3_WR_TIDEMARK */
    volatile uint32_t  _pad_0x44_0x107[49];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod;               /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_H2F. */
typedef volatile struct ALT_L3_MST_H2F_raw_s  ALT_L3_MST_H2F_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : ACP - ALT_L3_MST_ACP
 * ACP
 * 
 * Registers associated with the ACP master. This master is used to access the MPU
 * ACP slave via the ACP ID Mapper.
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
 * The struct declaration for register group ALT_L3_MST_ACP.
 */
struct ALT_L3_MST_ACP_s
{
    volatile uint32_t                _pad_0x0_0x7[2];     /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;       /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t                _pad_0xc_0x107[63];  /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_t         fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_MST_ACP. */
typedef volatile struct ALT_L3_MST_ACP_s  ALT_L3_MST_ACP_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_ACP. */
struct ALT_L3_MST_ACP_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];     /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;       /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x107[63];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_ACP. */
typedef volatile struct ALT_L3_MST_ACP_raw_s  ALT_L3_MST_ACP_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : Boot ROM - ALT_L3_MST_ROM
 * Boot ROM
 * 
 * Registers associated with the Boot ROM master. This master is used to access the
 * contents of the Boot ROM.
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
 * The struct declaration for register group ALT_L3_MST_ROM.
 */
struct ALT_L3_MST_ROM_s
{
    volatile uint32_t                _pad_0x0_0x7[2];     /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;       /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t                _pad_0xc_0x107[63];  /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_t         fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_MST_ROM. */
typedef volatile struct ALT_L3_MST_ROM_s  ALT_L3_MST_ROM_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_ROM. */
struct ALT_L3_MST_ROM_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];     /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;       /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x107[63];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_ROM. */
typedef volatile struct ALT_L3_MST_ROM_raw_s  ALT_L3_MST_ROM_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : On-chip RAM - ALT_L3_MST_OCRAM
 * On-chip RAM
 * 
 * Registers associated with the On-chip RAM master. This master is used to access
 * the contents of the On-chip RAM.
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
 * The struct declaration for register group ALT_L3_MST_OCRAM.
 */
struct ALT_L3_MST_OCRAM_s
{
    volatile uint32_t                _pad_0x0_0x7[2];      /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_BM_ISS_t  fn_mod_bm_iss;        /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t                _pad_0xc_0x3f[13];    /* *UNDEFINED* */
    volatile ALT_L3_WR_TIDEMARK_t    wr_tidemark;          /* ALT_L3_WR_TIDEMARK */
    volatile uint32_t                _pad_0x44_0x107[49];  /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_t         fn_mod;               /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_MST_OCRAM. */
typedef volatile struct ALT_L3_MST_OCRAM_s  ALT_L3_MST_OCRAM_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MST_OCRAM. */
struct ALT_L3_MST_OCRAM_raw_s
{
    volatile uint32_t  _pad_0x0_0x7[2];      /* *UNDEFINED* */
    volatile uint32_t  fn_mod_bm_iss;        /* ALT_L3_FN_MOD_BM_ISS */
    volatile uint32_t  _pad_0xc_0x3f[13];    /* *UNDEFINED* */
    volatile uint32_t  wr_tidemark;          /* ALT_L3_WR_TIDEMARK */
    volatile uint32_t  _pad_0x44_0x107[49];  /* *UNDEFINED* */
    volatile uint32_t  fn_mod;               /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MST_OCRAM. */
typedef volatile struct ALT_L3_MST_OCRAM_raw_s  ALT_L3_MST_OCRAM_raw_t;
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
 * The struct declaration for register group ALT_L3_MSTGRP.
 */
struct ALT_L3_MSTGRP_s
{
    volatile ALT_L3_MST_L4MAIN_t       mastergrp_l4main;            /* ALT_L3_MST_L4MAIN */
    volatile uint32_t                  _pad_0xc_0xfff[1021];        /* *UNDEFINED* */
    volatile ALT_L3_MST_L4SP_t         mastergrp_l4sp;              /* ALT_L3_MST_L4SP */
    volatile uint32_t                  _pad_0x100c_0x1fff[1021];    /* *UNDEFINED* */
    volatile ALT_L3_MST_L4MP_t         mastergrp_l4mp;              /* ALT_L3_MST_L4MP */
    volatile uint32_t                  _pad_0x200c_0x2fff[1021];    /* *UNDEFINED* */
    volatile ALT_L3_MST_L4OSC1_t       mastergrp_l4osc1;            /* ALT_L3_MST_L4OSC1 */
    volatile uint32_t                  _pad_0x300c_0x3fff[1021];    /* *UNDEFINED* */
    volatile ALT_L3_MST_L4SPIM_t       mastergrp_l4spim;            /* ALT_L3_MST_L4SPIM */
    volatile uint32_t                  _pad_0x400c_0x4fff[1021];    /* *UNDEFINED* */
    volatile ALT_L3_MST_STM_t          mastergrp_stm;               /* ALT_L3_MST_STM */
    volatile uint32_t                  _pad_0x510c_0x5fff[957];     /* *UNDEFINED* */
    volatile ALT_L3_MST_LWH2F_t        mastergrp_lwhps2fpga;        /* ALT_L3_MST_LWH2F */
    volatile uint32_t                  _pad_0x610c_0x7fff[1981];    /* *UNDEFINED* */
    volatile ALT_L3_MST_USB1_t         mastergrp_usb1;              /* ALT_L3_MST_USB1 */
    volatile uint32_t                  _pad_0x8048_0x8fff[1006];    /* *UNDEFINED* */
    volatile ALT_L3_MST_NANDDATA_t     mastergrp_nanddata;          /* ALT_L3_MST_NANDDATA */
    volatile uint32_t                  _pad_0x910c_0x1dfff[21437];  /* *UNDEFINED* */
    volatile ALT_L3_MST_USB0_t         mastergrp_usb0;              /* ALT_L3_MST_USB0 */
    volatile uint32_t                  _pad_0x1e048_0x1efff[1006];  /* *UNDEFINED* */
    volatile ALT_L3_MST_NAND_t         mastergrp_nandregs;          /* ALT_L3_MST_NAND */
    volatile uint32_t                  _pad_0x1f10c_0x1ffff[957];   /* *UNDEFINED* */
    volatile ALT_L3_MST_QSPIDATA_t     mastergrp_qspidata;          /* ALT_L3_MST_QSPIDATA */
    volatile uint32_t                  _pad_0x20048_0x20fff[1006];  /* *UNDEFINED* */
    volatile ALT_L3_MST_FPGAMGRDATA_t  mastergrp_fpgamgrdata;       /* ALT_L3_MST_FPGAMGRDATA */
    volatile uint32_t                  _pad_0x2110c_0x21fff[957];   /* *UNDEFINED* */
    volatile ALT_L3_MST_H2F_t          mastergrp_hps2fpga;          /* ALT_L3_MST_H2F */
    volatile uint32_t                  _pad_0x2210c_0x22fff[957];   /* *UNDEFINED* */
    volatile ALT_L3_MST_ACP_t          mastergrp_acp;               /* ALT_L3_MST_ACP */
    volatile uint32_t                  _pad_0x2310c_0x23fff[957];   /* *UNDEFINED* */
    volatile ALT_L3_MST_ROM_t          mastergrp_rom;               /* ALT_L3_MST_ROM */
    volatile uint32_t                  _pad_0x2410c_0x24fff[957];   /* *UNDEFINED* */
    volatile ALT_L3_MST_OCRAM_t        mastergrp_ocram;             /* ALT_L3_MST_OCRAM */
};

/* The typedef declaration for register group ALT_L3_MSTGRP. */
typedef volatile struct ALT_L3_MSTGRP_s  ALT_L3_MSTGRP_t;
/* The struct declaration for the raw register contents of register group ALT_L3_MSTGRP. */
struct ALT_L3_MSTGRP_raw_s
{
    volatile ALT_L3_MST_L4MAIN_raw_t       mastergrp_l4main;            /* ALT_L3_MST_L4MAIN */
    volatile uint32_t                      _pad_0xc_0xfff[1021];        /* *UNDEFINED* */
    volatile ALT_L3_MST_L4SP_raw_t         mastergrp_l4sp;              /* ALT_L3_MST_L4SP */
    volatile uint32_t                      _pad_0x100c_0x1fff[1021];    /* *UNDEFINED* */
    volatile ALT_L3_MST_L4MP_raw_t         mastergrp_l4mp;              /* ALT_L3_MST_L4MP */
    volatile uint32_t                      _pad_0x200c_0x2fff[1021];    /* *UNDEFINED* */
    volatile ALT_L3_MST_L4OSC1_raw_t       mastergrp_l4osc1;            /* ALT_L3_MST_L4OSC1 */
    volatile uint32_t                      _pad_0x300c_0x3fff[1021];    /* *UNDEFINED* */
    volatile ALT_L3_MST_L4SPIM_raw_t       mastergrp_l4spim;            /* ALT_L3_MST_L4SPIM */
    volatile uint32_t                      _pad_0x400c_0x4fff[1021];    /* *UNDEFINED* */
    volatile ALT_L3_MST_STM_raw_t          mastergrp_stm;               /* ALT_L3_MST_STM */
    volatile uint32_t                      _pad_0x510c_0x5fff[957];     /* *UNDEFINED* */
    volatile ALT_L3_MST_LWH2F_raw_t        mastergrp_lwhps2fpga;        /* ALT_L3_MST_LWH2F */
    volatile uint32_t                      _pad_0x610c_0x7fff[1981];    /* *UNDEFINED* */
    volatile ALT_L3_MST_USB1_raw_t         mastergrp_usb1;              /* ALT_L3_MST_USB1 */
    volatile uint32_t                      _pad_0x8048_0x8fff[1006];    /* *UNDEFINED* */
    volatile ALT_L3_MST_NANDDATA_raw_t     mastergrp_nanddata;          /* ALT_L3_MST_NANDDATA */
    volatile uint32_t                      _pad_0x910c_0x1dfff[21437];  /* *UNDEFINED* */
    volatile ALT_L3_MST_USB0_raw_t         mastergrp_usb0;              /* ALT_L3_MST_USB0 */
    volatile uint32_t                      _pad_0x1e048_0x1efff[1006];  /* *UNDEFINED* */
    volatile ALT_L3_MST_NAND_raw_t         mastergrp_nandregs;          /* ALT_L3_MST_NAND */
    volatile uint32_t                      _pad_0x1f10c_0x1ffff[957];   /* *UNDEFINED* */
    volatile ALT_L3_MST_QSPIDATA_raw_t     mastergrp_qspidata;          /* ALT_L3_MST_QSPIDATA */
    volatile uint32_t                      _pad_0x20048_0x20fff[1006];  /* *UNDEFINED* */
    volatile ALT_L3_MST_FPGAMGRDATA_raw_t  mastergrp_fpgamgrdata;       /* ALT_L3_MST_FPGAMGRDATA */
    volatile uint32_t                      _pad_0x2110c_0x21fff[957];   /* *UNDEFINED* */
    volatile ALT_L3_MST_H2F_raw_t          mastergrp_hps2fpga;          /* ALT_L3_MST_H2F */
    volatile uint32_t                      _pad_0x2210c_0x22fff[957];   /* *UNDEFINED* */
    volatile ALT_L3_MST_ACP_raw_t          mastergrp_acp;               /* ALT_L3_MST_ACP */
    volatile uint32_t                      _pad_0x2310c_0x23fff[957];   /* *UNDEFINED* */
    volatile ALT_L3_MST_ROM_raw_t          mastergrp_rom;               /* ALT_L3_MST_ROM */
    volatile uint32_t                      _pad_0x2410c_0x24fff[957];   /* *UNDEFINED* */
    volatile ALT_L3_MST_OCRAM_raw_t        mastergrp_ocram;             /* ALT_L3_MST_OCRAM */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_MSTGRP. */
typedef volatile struct ALT_L3_MSTGRP_raw_s  ALT_L3_MSTGRP_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : Slave Register Group - ALT_L3_SLVGRP
 * Slave Register Group
 * 
 * Registers associated with slave interfaces.
 * 
 */
/*
 * Register Group : DAP - ALT_L3_SLV_DAP
 * DAP
 * 
 * Registers associated with the DAP slave interface. This slave is used by the DAP
 * to access slaves attached to the L3/L4 Interconnect.
 * 
 */
/*
 * Register : Functionality Modification 2 Register - fn_mod2
 * 
 * Controls bypass merge of upsizing/downsizing.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description 
 * :-------|:-------|:------|:-------------
 *  [0]    | RW     | 0x0   | Bypass Merge
 *  [31:1] | ???    | 0x0   | *UNDEFINED* 
 * 
 */
/*
 * Field : Bypass Merge - bypass_merge
 * 
 * Controls bypass merge of upsizing/downsizing.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                  | Value | Description                                     
 * :--------------------------------------|:------|:-------------------------------------------------
 *  ALT_L3_FN_MOD2_BYPASS_MERGE_E_ALTER   | 0x0   | The network can alter transactions.             
 *  ALT_L3_FN_MOD2_BYPASS_MERGE_E_NOALTER | 0x1   | The network does not alter any transactions that
 * :                                      |       | could pass through the upsizer legally without  
 * :                                      |       | alteration.                                     
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_FN_MOD2_BYPASS_MERGE
 * 
 * The network can alter transactions.
 */
#define ALT_L3_FN_MOD2_BYPASS_MERGE_E_ALTER     0x0
/*
 * Enumerated value for register field ALT_L3_FN_MOD2_BYPASS_MERGE
 * 
 * The network does not alter any transactions that could pass through the upsizer
 * legally without alteration.
 */
#define ALT_L3_FN_MOD2_BYPASS_MERGE_E_NOALTER   0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_FN_MOD2_BYPASS_MERGE register field. */
#define ALT_L3_FN_MOD2_BYPASS_MERGE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_FN_MOD2_BYPASS_MERGE register field. */
#define ALT_L3_FN_MOD2_BYPASS_MERGE_MSB        0
/* The width in bits of the ALT_L3_FN_MOD2_BYPASS_MERGE register field. */
#define ALT_L3_FN_MOD2_BYPASS_MERGE_WIDTH      1
/* The mask used to set the ALT_L3_FN_MOD2_BYPASS_MERGE register field value. */
#define ALT_L3_FN_MOD2_BYPASS_MERGE_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_FN_MOD2_BYPASS_MERGE register field value. */
#define ALT_L3_FN_MOD2_BYPASS_MERGE_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_FN_MOD2_BYPASS_MERGE register field. */
#define ALT_L3_FN_MOD2_BYPASS_MERGE_RESET      0x0
/* Extracts the ALT_L3_FN_MOD2_BYPASS_MERGE field value from a register. */
#define ALT_L3_FN_MOD2_BYPASS_MERGE_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_FN_MOD2_BYPASS_MERGE register field value suitable for setting the register. */
#define ALT_L3_FN_MOD2_BYPASS_MERGE_SET(value) (((value) << 0) & 0x00000001)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_FN_MOD2.
 */
struct ALT_L3_FN_MOD2_s
{
    uint32_t  bypass_merge :  1;  /* Bypass Merge */
    uint32_t               : 31;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_FN_MOD2. */
typedef volatile struct ALT_L3_FN_MOD2_s  ALT_L3_FN_MOD2_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_FN_MOD2 register from the beginning of the component. */
#define ALT_L3_FN_MOD2_OFST        0x24
/* The address of the ALT_L3_FN_MOD2 register. */
#define ALT_L3_FN_MOD2_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L3_FN_MOD2_OFST))

/*
 * Register : Functionality Modification AHB Register - fn_mod_ahb
 * 
 * Controls how AHB-lite burst transactions are converted to AXI tranactions.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description             
 * :-------|:-------|:------|:-------------------------
 *  [0]    | RW     | 0x0   | Read Increment Override 
 *  [1]    | RW     | 0x0   | Write Increment Override
 *  [31:2] | ???    | 0x0   | *UNDEFINED*             
 * 
 */
/*
 * Field : Read Increment Override - rd_incr_override
 * 
 * Controls how AHB-lite read burst transactions are converted to AXI tranactions.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                         | Value | Description                                  
 * :---------------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE_E_DEFAULT | 0x0   | The L3 Interconnect converts AHB-lite read   
 * :                                             |       | bursts to AXI transactions in accordance with
 * :                                             |       | the default behavior as specified in the ARM 
 * :                                             |       | NIC-301 documentation.                       
 *  ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE_E_SINGLES | 0x1   | The L3 Interconnect converts AHB-lite read   
 * :                                             |       | bursts to AXI single transactions.           
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE
 * 
 * The L3 Interconnect converts AHB-lite read bursts to AXI transactions in
 * accordance with the default behavior as specified in the ARM NIC-301
 * documentation.
 */
#define ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE_E_DEFAULT    0x0
/*
 * Enumerated value for register field ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE
 * 
 * The L3 Interconnect converts AHB-lite read bursts to AXI single transactions.
 */
#define ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE_E_SINGLES    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE register field. */
#define ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE register field. */
#define ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE_MSB        0
/* The width in bits of the ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE register field. */
#define ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE_WIDTH      1
/* The mask used to set the ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE register field value. */
#define ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE_SET_MSK    0x00000001
/* The mask used to clear the ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE register field value. */
#define ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE_CLR_MSK    0xfffffffe
/* The reset value of the ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE register field. */
#define ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE_RESET      0x0
/* Extracts the ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE field value from a register. */
#define ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE_GET(value) (((value) & 0x00000001) >> 0)
/* Produces a ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE register field value suitable for setting the register. */
#define ALT_L3_FN_MOD_AHB_RD_INCR_OVERRIDE_SET(value) (((value) << 0) & 0x00000001)

/*
 * Field : Write Increment Override - wr_incr_override
 * 
 * Controls how AHB-lite write burst transactions are converted to AXI tranactions.
 * 
 * Field Enumeration Values:
 * 
 *  Enum                                         | Value | Description                                  
 * :---------------------------------------------|:------|:----------------------------------------------
 *  ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE_E_DEFAULT | 0x0   | The L3 Interconnect converts AHB-lite write  
 * :                                             |       | bursts to AXI transactions in accordance with
 * :                                             |       | the default behavior as specified in the ARM 
 * :                                             |       | NIC-301 documentation.                       
 *  ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE_E_SINGLES | 0x1   | The L3 Interconnect converts AHB-lite write  
 * :                                             |       | bursts to AXI single transactions.           
 * 
 * Field Access Macros:
 * 
 */
/*
 * Enumerated value for register field ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE
 * 
 * The L3 Interconnect converts AHB-lite write bursts to AXI transactions in
 * accordance with the default behavior as specified in the ARM NIC-301
 * documentation.
 */
#define ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE_E_DEFAULT    0x0
/*
 * Enumerated value for register field ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE
 * 
 * The L3 Interconnect converts AHB-lite write bursts to AXI single transactions.
 */
#define ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE_E_SINGLES    0x1

/* The Least Significant Bit (LSB) position of the ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE register field. */
#define ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE_LSB        1
/* The Most Significant Bit (MSB) position of the ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE register field. */
#define ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE_MSB        1
/* The width in bits of the ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE register field. */
#define ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE_WIDTH      1
/* The mask used to set the ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE register field value. */
#define ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE_SET_MSK    0x00000002
/* The mask used to clear the ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE register field value. */
#define ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE_CLR_MSK    0xfffffffd
/* The reset value of the ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE register field. */
#define ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE_RESET      0x0
/* Extracts the ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE field value from a register. */
#define ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE_GET(value) (((value) & 0x00000002) >> 1)
/* Produces a ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE register field value suitable for setting the register. */
#define ALT_L3_FN_MOD_AHB_WR_INCR_OVERRIDE_SET(value) (((value) << 1) & 0x00000002)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_FN_MOD_AHB.
 */
struct ALT_L3_FN_MOD_AHB_s
{
    uint32_t  rd_incr_override :  1;  /* Read Increment Override */
    uint32_t  wr_incr_override :  1;  /* Write Increment Override */
    uint32_t                   : 30;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_FN_MOD_AHB. */
typedef volatile struct ALT_L3_FN_MOD_AHB_s  ALT_L3_FN_MOD_AHB_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_FN_MOD_AHB register from the beginning of the component. */
#define ALT_L3_FN_MOD_AHB_OFST        0x28
/* The address of the ALT_L3_FN_MOD_AHB register. */
#define ALT_L3_FN_MOD_AHB_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L3_FN_MOD_AHB_OFST))

/*
 * Register : Read Channel QoS Value - read_qos
 * 
 * QoS (Quality of Service) value for the read channel.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [3:0]  | RW     | 0x0   | Priority   
 *  [31:4] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Priority - pri
 * 
 * QoS (Quality of Service) value for the read channel. A higher value has a higher
 * priority.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_L3_RD_QOS_PRI register field. */
#define ALT_L3_RD_QOS_PRI_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_RD_QOS_PRI register field. */
#define ALT_L3_RD_QOS_PRI_MSB        3
/* The width in bits of the ALT_L3_RD_QOS_PRI register field. */
#define ALT_L3_RD_QOS_PRI_WIDTH      4
/* The mask used to set the ALT_L3_RD_QOS_PRI register field value. */
#define ALT_L3_RD_QOS_PRI_SET_MSK    0x0000000f
/* The mask used to clear the ALT_L3_RD_QOS_PRI register field value. */
#define ALT_L3_RD_QOS_PRI_CLR_MSK    0xfffffff0
/* The reset value of the ALT_L3_RD_QOS_PRI register field. */
#define ALT_L3_RD_QOS_PRI_RESET      0x0
/* Extracts the ALT_L3_RD_QOS_PRI field value from a register. */
#define ALT_L3_RD_QOS_PRI_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_L3_RD_QOS_PRI register field value suitable for setting the register. */
#define ALT_L3_RD_QOS_PRI_SET(value) (((value) << 0) & 0x0000000f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_RD_QOS.
 */
struct ALT_L3_RD_QOS_s
{
    uint32_t  pri :  4;  /* Priority */
    uint32_t      : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_RD_QOS. */
typedef volatile struct ALT_L3_RD_QOS_s  ALT_L3_RD_QOS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_RD_QOS register from the beginning of the component. */
#define ALT_L3_RD_QOS_OFST        0x100
/* The address of the ALT_L3_RD_QOS register. */
#define ALT_L3_RD_QOS_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L3_RD_QOS_OFST))

/*
 * Register : Write Channel QoS Value - write_qos
 * 
 * QoS (Quality of Service) value for the write channel.
 * 
 * Register Layout
 * 
 *  Bits   | Access | Reset | Description
 * :-------|:-------|:------|:------------
 *  [3:0]  | RW     | 0x0   | Priority   
 *  [31:4] | ???    | 0x0   | *UNDEFINED*
 * 
 */
/*
 * Field : Priority - pri
 * 
 * QoS (Quality of Service) value for the write channel. A higher value has a
 * higher priority.
 * 
 * Field Access Macros:
 * 
 */
/* The Least Significant Bit (LSB) position of the ALT_L3_WR_QOS_PRI register field. */
#define ALT_L3_WR_QOS_PRI_LSB        0
/* The Most Significant Bit (MSB) position of the ALT_L3_WR_QOS_PRI register field. */
#define ALT_L3_WR_QOS_PRI_MSB        3
/* The width in bits of the ALT_L3_WR_QOS_PRI register field. */
#define ALT_L3_WR_QOS_PRI_WIDTH      4
/* The mask used to set the ALT_L3_WR_QOS_PRI register field value. */
#define ALT_L3_WR_QOS_PRI_SET_MSK    0x0000000f
/* The mask used to clear the ALT_L3_WR_QOS_PRI register field value. */
#define ALT_L3_WR_QOS_PRI_CLR_MSK    0xfffffff0
/* The reset value of the ALT_L3_WR_QOS_PRI register field. */
#define ALT_L3_WR_QOS_PRI_RESET      0x0
/* Extracts the ALT_L3_WR_QOS_PRI field value from a register. */
#define ALT_L3_WR_QOS_PRI_GET(value) (((value) & 0x0000000f) >> 0)
/* Produces a ALT_L3_WR_QOS_PRI register field value suitable for setting the register. */
#define ALT_L3_WR_QOS_PRI_SET(value) (((value) << 0) & 0x0000000f)

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register ALT_L3_WR_QOS.
 */
struct ALT_L3_WR_QOS_s
{
    uint32_t  pri :  4;  /* Priority */
    uint32_t      : 28;  /* *UNDEFINED* */
};

/* The typedef declaration for register ALT_L3_WR_QOS. */
typedef volatile struct ALT_L3_WR_QOS_s  ALT_L3_WR_QOS_t;
#endif  /* __ASSEMBLY__ */

/* The byte offset of the ALT_L3_WR_QOS register from the beginning of the component. */
#define ALT_L3_WR_QOS_OFST        0x104
/* The address of the ALT_L3_WR_QOS register. */
#define ALT_L3_WR_QOS_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_L3_WR_QOS_OFST))

#ifndef __ASSEMBLY__
/*
 * WARNING: The C register and register group struct declarations are provided for
 * convenience and illustrative purposes. They should, however, be used with
 * caution as the C language standard provides no guarantees about the alignment or
 * atomicity of device memory accesses. The recommended practice for writing
 * hardware drivers is to use the SoCAL access macros and alt_read_word() and
 * alt_write_word() functions.
 * 
 * The struct declaration for register group ALT_L3_SLV_DAP.
 */
struct ALT_L3_SLV_DAP_s
{
    volatile uint32_t             _pad_0x0_0x23[9];    /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD2_t     fn_mod2;             /* ALT_L3_FN_MOD2 */
    volatile ALT_L3_FN_MOD_AHB_t  fn_mod_ahb;          /* ALT_L3_FN_MOD_AHB */
    volatile uint32_t             _pad_0x2c_0xff[53];  /* *UNDEFINED* */
    volatile ALT_L3_RD_QOS_t      read_qos;            /* ALT_L3_RD_QOS */
    volatile ALT_L3_WR_QOS_t      write_qos;           /* ALT_L3_WR_QOS */
    volatile ALT_L3_FN_MOD_t      fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_SLV_DAP. */
typedef volatile struct ALT_L3_SLV_DAP_s  ALT_L3_SLV_DAP_t;
/* The struct declaration for the raw register contents of register group ALT_L3_SLV_DAP. */
struct ALT_L3_SLV_DAP_raw_s
{
    volatile uint32_t  _pad_0x0_0x23[9];    /* *UNDEFINED* */
    volatile uint32_t  fn_mod2;             /* ALT_L3_FN_MOD2 */
    volatile uint32_t  fn_mod_ahb;          /* ALT_L3_FN_MOD_AHB */
    volatile uint32_t  _pad_0x2c_0xff[53];  /* *UNDEFINED* */
    volatile uint32_t  read_qos;            /* ALT_L3_RD_QOS */
    volatile uint32_t  write_qos;           /* ALT_L3_WR_QOS */
    volatile uint32_t  fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_SLV_DAP. */
typedef volatile struct ALT_L3_SLV_DAP_raw_s  ALT_L3_SLV_DAP_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : MPU - ALT_L3_SLV_MPU
 * MPU
 * 
 * Registers associated with the MPU slave interface. This slave is used by the MPU
 * to access slaves attached to the L3/L4 Interconnect.
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
 * The struct declaration for register group ALT_L3_SLV_MPU.
 */
struct ALT_L3_SLV_MPU_s
{
    volatile uint32_t         _pad_0x0_0xff[64];  /* *UNDEFINED* */
    volatile ALT_L3_RD_QOS_t  read_qos;           /* ALT_L3_RD_QOS */
    volatile ALT_L3_WR_QOS_t  write_qos;          /* ALT_L3_WR_QOS */
    volatile ALT_L3_FN_MOD_t  fn_mod;             /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_SLV_MPU. */
typedef volatile struct ALT_L3_SLV_MPU_s  ALT_L3_SLV_MPU_t;
/* The struct declaration for the raw register contents of register group ALT_L3_SLV_MPU. */
struct ALT_L3_SLV_MPU_raw_s
{
    volatile uint32_t  _pad_0x0_0xff[64];  /* *UNDEFINED* */
    volatile uint32_t  read_qos;           /* ALT_L3_RD_QOS */
    volatile uint32_t  write_qos;          /* ALT_L3_WR_QOS */
    volatile uint32_t  fn_mod;             /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_SLV_MPU. */
typedef volatile struct ALT_L3_SLV_MPU_raw_s  ALT_L3_SLV_MPU_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : SDMMC - ALT_L3_SLV_SDMMC
 * SDMMC
 * 
 * Registers associated with the SDMMC slave interface. This slave is used by the
 * DMA controller built into the SDMMC to access slaves attached to the L3/L4
 * Interconnect.
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
 * The struct declaration for register group ALT_L3_SLV_SDMMC.
 */
struct ALT_L3_SLV_SDMMC_s
{
    volatile uint32_t             _pad_0x0_0x27[10];   /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_AHB_t  fn_mod_ahb;          /* ALT_L3_FN_MOD_AHB */
    volatile uint32_t             _pad_0x2c_0xff[53];  /* *UNDEFINED* */
    volatile ALT_L3_RD_QOS_t      read_qos;            /* ALT_L3_RD_QOS */
    volatile ALT_L3_WR_QOS_t      write_qos;           /* ALT_L3_WR_QOS */
    volatile ALT_L3_FN_MOD_t      fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_SLV_SDMMC. */
typedef volatile struct ALT_L3_SLV_SDMMC_s  ALT_L3_SLV_SDMMC_t;
/* The struct declaration for the raw register contents of register group ALT_L3_SLV_SDMMC. */
struct ALT_L3_SLV_SDMMC_raw_s
{
    volatile uint32_t  _pad_0x0_0x27[10];   /* *UNDEFINED* */
    volatile uint32_t  fn_mod_ahb;          /* ALT_L3_FN_MOD_AHB */
    volatile uint32_t  _pad_0x2c_0xff[53];  /* *UNDEFINED* */
    volatile uint32_t  read_qos;            /* ALT_L3_RD_QOS */
    volatile uint32_t  write_qos;           /* ALT_L3_WR_QOS */
    volatile uint32_t  fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_SLV_SDMMC. */
typedef volatile struct ALT_L3_SLV_SDMMC_raw_s  ALT_L3_SLV_SDMMC_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : DMA - ALT_L3_SLV_DMA
 * DMA
 * 
 * Registers associated with the DMA Controller slave interface. This slave is used
 * by the DMA Controller to access slaves attached to the L3/L4 Interconnect.
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
 * The struct declaration for register group ALT_L3_SLV_DMA.
 */
struct ALT_L3_SLV_DMA_s
{
    volatile uint32_t         _pad_0x0_0xff[64];  /* *UNDEFINED* */
    volatile ALT_L3_RD_QOS_t  read_qos;           /* ALT_L3_RD_QOS */
    volatile ALT_L3_WR_QOS_t  write_qos;          /* ALT_L3_WR_QOS */
    volatile ALT_L3_FN_MOD_t  fn_mod;             /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_SLV_DMA. */
typedef volatile struct ALT_L3_SLV_DMA_s  ALT_L3_SLV_DMA_t;
/* The struct declaration for the raw register contents of register group ALT_L3_SLV_DMA. */
struct ALT_L3_SLV_DMA_raw_s
{
    volatile uint32_t  _pad_0x0_0xff[64];  /* *UNDEFINED* */
    volatile uint32_t  read_qos;           /* ALT_L3_RD_QOS */
    volatile uint32_t  write_qos;          /* ALT_L3_WR_QOS */
    volatile uint32_t  fn_mod;             /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_SLV_DMA. */
typedef volatile struct ALT_L3_SLV_DMA_raw_s  ALT_L3_SLV_DMA_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : FPGA2HPS - ALT_L3_SLV_F2H
 * FPGA2HPS
 * 
 * Registers associated with the FPGA2HPS AXI Bridge slave interface. This slave is
 * used by the FPGA2HPS AXI Bridge to access slaves attached to the L3/L4
 * Interconnect.
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
 * The struct declaration for register group ALT_L3_SLV_F2H.
 */
struct ALT_L3_SLV_F2H_s
{
    volatile uint32_t              _pad_0x0_0x3f[16];   /* *UNDEFINED* */
    volatile ALT_L3_WR_TIDEMARK_t  wr_tidemark;         /* ALT_L3_WR_TIDEMARK */
    volatile uint32_t              _pad_0x44_0xff[47];  /* *UNDEFINED* */
    volatile ALT_L3_RD_QOS_t       read_qos;            /* ALT_L3_RD_QOS */
    volatile ALT_L3_WR_QOS_t       write_qos;           /* ALT_L3_WR_QOS */
    volatile ALT_L3_FN_MOD_t       fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_SLV_F2H. */
typedef volatile struct ALT_L3_SLV_F2H_s  ALT_L3_SLV_F2H_t;
/* The struct declaration for the raw register contents of register group ALT_L3_SLV_F2H. */
struct ALT_L3_SLV_F2H_raw_s
{
    volatile uint32_t  _pad_0x0_0x3f[16];   /* *UNDEFINED* */
    volatile uint32_t  wr_tidemark;         /* ALT_L3_WR_TIDEMARK */
    volatile uint32_t  _pad_0x44_0xff[47];  /* *UNDEFINED* */
    volatile uint32_t  read_qos;            /* ALT_L3_RD_QOS */
    volatile uint32_t  write_qos;           /* ALT_L3_WR_QOS */
    volatile uint32_t  fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_SLV_F2H. */
typedef volatile struct ALT_L3_SLV_F2H_raw_s  ALT_L3_SLV_F2H_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : ETR - ALT_L3_SLV_ETR
 * ETR
 * 
 * Registers associated with the ETR (TMC) slave interface. This slave is used by
 * the ETR to access slaves attached to the L3/L4 Interconnect.
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
 * The struct declaration for register group ALT_L3_SLV_ETR.
 */
struct ALT_L3_SLV_ETR_s
{
    volatile uint32_t         _pad_0x0_0xff[64];  /* *UNDEFINED* */
    volatile ALT_L3_RD_QOS_t  read_qos;           /* ALT_L3_RD_QOS */
    volatile ALT_L3_WR_QOS_t  write_qos;          /* ALT_L3_WR_QOS */
    volatile ALT_L3_FN_MOD_t  fn_mod;             /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_SLV_ETR. */
typedef volatile struct ALT_L3_SLV_ETR_s  ALT_L3_SLV_ETR_t;
/* The struct declaration for the raw register contents of register group ALT_L3_SLV_ETR. */
struct ALT_L3_SLV_ETR_raw_s
{
    volatile uint32_t  _pad_0x0_0xff[64];  /* *UNDEFINED* */
    volatile uint32_t  read_qos;           /* ALT_L3_RD_QOS */
    volatile uint32_t  write_qos;          /* ALT_L3_WR_QOS */
    volatile uint32_t  fn_mod;             /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_SLV_ETR. */
typedef volatile struct ALT_L3_SLV_ETR_raw_s  ALT_L3_SLV_ETR_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : EMAC0 - ALT_L3_SLV_EMAC0
 * EMAC0
 * 
 * Registers associated with the EMAC0 slave interface. This slave is used by the
 * DMA controller built into the EMAC0 to access slaves attached to the L3/L4
 * Interconnect.
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
 * The struct declaration for register group ALT_L3_SLV_EMAC0.
 */
struct ALT_L3_SLV_EMAC0_s
{
    volatile uint32_t         _pad_0x0_0xff[64];  /* *UNDEFINED* */
    volatile ALT_L3_RD_QOS_t  read_qos;           /* ALT_L3_RD_QOS */
    volatile ALT_L3_WR_QOS_t  write_qos;          /* ALT_L3_WR_QOS */
    volatile ALT_L3_FN_MOD_t  fn_mod;             /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_SLV_EMAC0. */
typedef volatile struct ALT_L3_SLV_EMAC0_s  ALT_L3_SLV_EMAC0_t;
/* The struct declaration for the raw register contents of register group ALT_L3_SLV_EMAC0. */
struct ALT_L3_SLV_EMAC0_raw_s
{
    volatile uint32_t  _pad_0x0_0xff[64];  /* *UNDEFINED* */
    volatile uint32_t  read_qos;           /* ALT_L3_RD_QOS */
    volatile uint32_t  write_qos;          /* ALT_L3_WR_QOS */
    volatile uint32_t  fn_mod;             /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_SLV_EMAC0. */
typedef volatile struct ALT_L3_SLV_EMAC0_raw_s  ALT_L3_SLV_EMAC0_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : EMAC1 - ALT_L3_SLV_EMAC1
 * EMAC1
 * 
 * Registers associated with the EMAC1 slave interface. This slave is used by the
 * DMA controller built into the EMAC1 to access slaves attached to the L3/L4
 * Interconnect.
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
 * The struct declaration for register group ALT_L3_SLV_EMAC1.
 */
struct ALT_L3_SLV_EMAC1_s
{
    volatile uint32_t         _pad_0x0_0xff[64];  /* *UNDEFINED* */
    volatile ALT_L3_RD_QOS_t  read_qos;           /* ALT_L3_RD_QOS */
    volatile ALT_L3_WR_QOS_t  write_qos;          /* ALT_L3_WR_QOS */
    volatile ALT_L3_FN_MOD_t  fn_mod;             /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_SLV_EMAC1. */
typedef volatile struct ALT_L3_SLV_EMAC1_s  ALT_L3_SLV_EMAC1_t;
/* The struct declaration for the raw register contents of register group ALT_L3_SLV_EMAC1. */
struct ALT_L3_SLV_EMAC1_raw_s
{
    volatile uint32_t  _pad_0x0_0xff[64];  /* *UNDEFINED* */
    volatile uint32_t  read_qos;           /* ALT_L3_RD_QOS */
    volatile uint32_t  write_qos;          /* ALT_L3_WR_QOS */
    volatile uint32_t  fn_mod;             /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_SLV_EMAC1. */
typedef volatile struct ALT_L3_SLV_EMAC1_raw_s  ALT_L3_SLV_EMAC1_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : USB0 - ALT_L3_SLV_USB0
 * USB0
 * 
 * Registers associated with the USB0 slave interface. This slave is used by the
 * DMA controller built into the USB0 to access slaves attached to the L3/L4
 * Interconnect.
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
 * The struct declaration for register group ALT_L3_SLV_USB0.
 */
struct ALT_L3_SLV_USB0_s
{
    volatile uint32_t             _pad_0x0_0x27[10];   /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_AHB_t  fn_mod_ahb;          /* ALT_L3_FN_MOD_AHB */
    volatile uint32_t             _pad_0x2c_0xff[53];  /* *UNDEFINED* */
    volatile ALT_L3_RD_QOS_t      read_qos;            /* ALT_L3_RD_QOS */
    volatile ALT_L3_WR_QOS_t      write_qos;           /* ALT_L3_WR_QOS */
    volatile ALT_L3_FN_MOD_t      fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_SLV_USB0. */
typedef volatile struct ALT_L3_SLV_USB0_s  ALT_L3_SLV_USB0_t;
/* The struct declaration for the raw register contents of register group ALT_L3_SLV_USB0. */
struct ALT_L3_SLV_USB0_raw_s
{
    volatile uint32_t  _pad_0x0_0x27[10];   /* *UNDEFINED* */
    volatile uint32_t  fn_mod_ahb;          /* ALT_L3_FN_MOD_AHB */
    volatile uint32_t  _pad_0x2c_0xff[53];  /* *UNDEFINED* */
    volatile uint32_t  read_qos;            /* ALT_L3_RD_QOS */
    volatile uint32_t  write_qos;           /* ALT_L3_WR_QOS */
    volatile uint32_t  fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_SLV_USB0. */
typedef volatile struct ALT_L3_SLV_USB0_raw_s  ALT_L3_SLV_USB0_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : NAND - ALT_L3_SLV_NAND
 * NAND
 * 
 * Registers associated with the NAND slave interface. This slave is used by the
 * DMA controller built into the NAND flash controller to access slaves attached to
 * the L3/L4 Interconnect.
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
 * The struct declaration for register group ALT_L3_SLV_NAND.
 */
struct ALT_L3_SLV_NAND_s
{
    volatile uint32_t         _pad_0x0_0xff[64];  /* *UNDEFINED* */
    volatile ALT_L3_RD_QOS_t  read_qos;           /* ALT_L3_RD_QOS */
    volatile ALT_L3_WR_QOS_t  write_qos;          /* ALT_L3_WR_QOS */
    volatile ALT_L3_FN_MOD_t  fn_mod;             /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_SLV_NAND. */
typedef volatile struct ALT_L3_SLV_NAND_s  ALT_L3_SLV_NAND_t;
/* The struct declaration for the raw register contents of register group ALT_L3_SLV_NAND. */
struct ALT_L3_SLV_NAND_raw_s
{
    volatile uint32_t  _pad_0x0_0xff[64];  /* *UNDEFINED* */
    volatile uint32_t  read_qos;           /* ALT_L3_RD_QOS */
    volatile uint32_t  write_qos;          /* ALT_L3_WR_QOS */
    volatile uint32_t  fn_mod;             /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_SLV_NAND. */
typedef volatile struct ALT_L3_SLV_NAND_raw_s  ALT_L3_SLV_NAND_raw_t;
#endif  /* __ASSEMBLY__ */


/*
 * Register Group : USB1 - ALT_L3_SLV_USB1
 * USB1
 * 
 * Registers associated with the USB1 slave interface. This slave is used by the
 * DMA controller built into the USB1 to access slaves attached to the L3/L4
 * Interconnect.
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
 * The struct declaration for register group ALT_L3_SLV_USB1.
 */
struct ALT_L3_SLV_USB1_s
{
    volatile uint32_t             _pad_0x0_0x27[10];   /* *UNDEFINED* */
    volatile ALT_L3_FN_MOD_AHB_t  fn_mod_ahb;          /* ALT_L3_FN_MOD_AHB */
    volatile uint32_t             _pad_0x2c_0xff[53];  /* *UNDEFINED* */
    volatile ALT_L3_RD_QOS_t      read_qos;            /* ALT_L3_RD_QOS */
    volatile ALT_L3_WR_QOS_t      write_qos;           /* ALT_L3_WR_QOS */
    volatile ALT_L3_FN_MOD_t      fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for register group ALT_L3_SLV_USB1. */
typedef volatile struct ALT_L3_SLV_USB1_s  ALT_L3_SLV_USB1_t;
/* The struct declaration for the raw register contents of register group ALT_L3_SLV_USB1. */
struct ALT_L3_SLV_USB1_raw_s
{
    volatile uint32_t  _pad_0x0_0x27[10];   /* *UNDEFINED* */
    volatile uint32_t  fn_mod_ahb;          /* ALT_L3_FN_MOD_AHB */
    volatile uint32_t  _pad_0x2c_0xff[53];  /* *UNDEFINED* */
    volatile uint32_t  read_qos;            /* ALT_L3_RD_QOS */
    volatile uint32_t  write_qos;           /* ALT_L3_WR_QOS */
    volatile uint32_t  fn_mod;              /* ALT_L3_FN_MOD */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_SLV_USB1. */
typedef volatile struct ALT_L3_SLV_USB1_raw_s  ALT_L3_SLV_USB1_raw_t;
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
 * The struct declaration for register group ALT_L3_SLVGRP.
 */
struct ALT_L3_SLVGRP_s
{
    volatile ALT_L3_SLV_DAP_t    slavegrp_dap;             /* ALT_L3_SLV_DAP */
    volatile uint32_t            _pad_0x10c_0xfff[957];    /* *UNDEFINED* */
    volatile ALT_L3_SLV_MPU_t    slavegrp_mpu;             /* ALT_L3_SLV_MPU */
    volatile uint32_t            _pad_0x110c_0x1fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_SDMMC_t  slavegrp_sdmmc;           /* ALT_L3_SLV_SDMMC */
    volatile uint32_t            _pad_0x210c_0x2fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_DMA_t    slavegrp_dma;             /* ALT_L3_SLV_DMA */
    volatile uint32_t            _pad_0x310c_0x3fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_F2H_t    slavegrp_fpga2hps;        /* ALT_L3_SLV_F2H */
    volatile uint32_t            _pad_0x410c_0x4fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_ETR_t    slavegrp_etr;             /* ALT_L3_SLV_ETR */
    volatile uint32_t            _pad_0x510c_0x5fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_EMAC0_t  slavegrp_emac0;           /* ALT_L3_SLV_EMAC0 */
    volatile uint32_t            _pad_0x610c_0x6fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_EMAC1_t  slavegrp_emac1;           /* ALT_L3_SLV_EMAC1 */
    volatile uint32_t            _pad_0x710c_0x7fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_USB0_t   slavegrp_usb0;            /* ALT_L3_SLV_USB0 */
    volatile uint32_t            _pad_0x810c_0x8fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_NAND_t   slavegrp_nand;            /* ALT_L3_SLV_NAND */
    volatile uint32_t            _pad_0x910c_0x9fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_USB1_t   slavegrp_usb1;            /* ALT_L3_SLV_USB1 */
};

/* The typedef declaration for register group ALT_L3_SLVGRP. */
typedef volatile struct ALT_L3_SLVGRP_s  ALT_L3_SLVGRP_t;
/* The struct declaration for the raw register contents of register group ALT_L3_SLVGRP. */
struct ALT_L3_SLVGRP_raw_s
{
    volatile ALT_L3_SLV_DAP_raw_t    slavegrp_dap;             /* ALT_L3_SLV_DAP */
    volatile uint32_t                _pad_0x10c_0xfff[957];    /* *UNDEFINED* */
    volatile ALT_L3_SLV_MPU_raw_t    slavegrp_mpu;             /* ALT_L3_SLV_MPU */
    volatile uint32_t                _pad_0x110c_0x1fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_SDMMC_raw_t  slavegrp_sdmmc;           /* ALT_L3_SLV_SDMMC */
    volatile uint32_t                _pad_0x210c_0x2fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_DMA_raw_t    slavegrp_dma;             /* ALT_L3_SLV_DMA */
    volatile uint32_t                _pad_0x310c_0x3fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_F2H_raw_t    slavegrp_fpga2hps;        /* ALT_L3_SLV_F2H */
    volatile uint32_t                _pad_0x410c_0x4fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_ETR_raw_t    slavegrp_etr;             /* ALT_L3_SLV_ETR */
    volatile uint32_t                _pad_0x510c_0x5fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_EMAC0_raw_t  slavegrp_emac0;           /* ALT_L3_SLV_EMAC0 */
    volatile uint32_t                _pad_0x610c_0x6fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_EMAC1_raw_t  slavegrp_emac1;           /* ALT_L3_SLV_EMAC1 */
    volatile uint32_t                _pad_0x710c_0x7fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_USB0_raw_t   slavegrp_usb0;            /* ALT_L3_SLV_USB0 */
    volatile uint32_t                _pad_0x810c_0x8fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_NAND_raw_t   slavegrp_nand;            /* ALT_L3_SLV_NAND */
    volatile uint32_t                _pad_0x910c_0x9fff[957];  /* *UNDEFINED* */
    volatile ALT_L3_SLV_USB1_raw_t   slavegrp_usb1;            /* ALT_L3_SLV_USB1 */
};

/* The typedef declaration for the raw register contents of register group ALT_L3_SLVGRP. */
typedef volatile struct ALT_L3_SLVGRP_raw_s  ALT_L3_SLVGRP_raw_t;
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
 * The struct declaration for register group ALT_L3.
 */
struct ALT_L3_s
{
    volatile ALT_L3_REMAP_t   remap;                        /* ALT_L3_REMAP */
    volatile uint32_t         _pad_0x4_0x7;                 /* *UNDEFINED* */
    volatile ALT_L3_SECGRP_t  secgrp;                       /* ALT_L3_SECGRP */
    volatile uint32_t         _pad_0xa4_0xfff[983];         /* *UNDEFINED* */
    volatile ALT_L3_IDGRP_t   idgrp;                        /* ALT_L3_IDGRP */
    volatile ALT_L3_MSTGRP_t  mastergrp;                    /* ALT_L3_MSTGRP */
    volatile uint32_t         _pad_0x2710c_0x41fff[27581];  /* *UNDEFINED* */
    volatile ALT_L3_SLVGRP_t  slavegrp;                     /* ALT_L3_SLVGRP */
    volatile uint32_t         _pad_0x4c10c_0x80000[53181];  /* *UNDEFINED* */
};

/* The typedef declaration for register group ALT_L3. */
typedef volatile struct ALT_L3_s  ALT_L3_t;
/* The struct declaration for the raw register contents of register group ALT_L3. */
struct ALT_L3_raw_s
{
    volatile uint32_t             remap;                        /* ALT_L3_REMAP */
    volatile uint32_t             _pad_0x4_0x7;                 /* *UNDEFINED* */
    volatile ALT_L3_SECGRP_raw_t  secgrp;                       /* ALT_L3_SECGRP */
    volatile uint32_t             _pad_0xa4_0xfff[983];         /* *UNDEFINED* */
    volatile ALT_L3_IDGRP_raw_t   idgrp;                        /* ALT_L3_IDGRP */
    volatile ALT_L3_MSTGRP_raw_t  mastergrp;                    /* ALT_L3_MSTGRP */
    volatile uint32_t             _pad_0x2710c_0x41fff[27581];  /* *UNDEFINED* */
    volatile ALT_L3_SLVGRP_raw_t  slavegrp;                     /* ALT_L3_SLVGRP */
    volatile uint32_t             _pad_0x4c10c_0x80000[53181];  /* *UNDEFINED* */
};

/* The typedef declaration for the raw register contents of register group ALT_L3. */
typedef volatile struct ALT_L3_raw_s  ALT_L3_raw_t;
#endif  /* __ASSEMBLY__ */


#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALTERA_ALT_L3_H__ */

