/** @file reg_i2c.h
 *   @brief I2C Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the I2C driver.
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#ifndef __REG_I2C_H__
#define __REG_I2C_H__

#include "sys_common.h"
#include "reg_gio.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* I2c Register Frame Definition */

/** @struct i2cBase
 *   @brief I2C Base Register Definition
 *
 *   This structure is used to access the I2C module registers.
 */

/** @typedef i2cBASE_t
 *   @brief I2C Register Frame Type Definition
 *
 *   This type is used to access the I2C Registers.
 */
typedef volatile struct i2cBase
{
    uint32 OAR; /**<  0x0000 I2C Own Address register               */
    uint32 IMR; /**<  0x0004 I2C Interrupt Mask/Status register     */
    uint32 STR; /**<  0x0008 I2C Interrupt Status register          */
    uint32 CKL; /**<  0x000C I2C Clock Divider Low register          */
    uint32 CKH; /**<  0x0010 I2C Clock Divider High register         */
    uint32 CNT; /**<  0x0014 I2C Data Count register                */
#if( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) )
    uint8 DRR;   /**< 0x0018: I2C Data Receive register,             */
    uint8 rsvd1; /**< 0x0018: I2C Data Receive register, Reserved    */
    uint8 rsvd2; /**< 0x0018: I2C Data Receive register, Reserved    */
    uint8 rsvd3; /**< 0x0018: I2C Data Receive register, Reserved    */
#else
    uint8 rsvd3; /**< 0x0018: I2C Data Receive register, Reserved    */
    uint8 rsvd2; /**< 0x0018: I2C Data Receive register, Reserved    */
    uint8 rsvd1; /**< 0x0018: I2C Data Receive register, Reserved    */
    uint8 DRR;   /**< 0x0018: I2C Data Receive register,             */
#endif
    uint32 SAR; /**<  0x001C I2C Slave Address register             */
#if( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) )
    uint8 DXR;   /**< 0x0020: I2C Data Transmit register,            */
    uint8 rsvd4; /**< 0x0020: I2C Data Transmit register, Reserved   */
    uint8 rsvd5; /**< 0x0020: I2C Data Transmit register, Reserved   */
    uint8 rsvd6; /**< 0x0020: I2C Data Transmit register, Reserved   */
#else
    uint8 rsvd6; /**< 0x0020: I2C Data Transmit register, Reserved   */
    uint8 rsvd5; /**< 0x0020: I2C Data Transmit register, Reserved   */
    uint8 rsvd4; /**< 0x0020: I2C Data Transmit register, Reserved   */
    uint8 DXR;   /**< 0x0020: I2C Data Transmit register,            */
#endif
    uint32 MDR;   /**<  0x0024 I2C Mode register                      */
    uint32 IVR;   /**<  0x0028 I2C Interrupt Vector register          */
    uint32 EMDR;  /**<  0x002C I2C Extended Mode register             */
    uint32 PSC;   /**<  0x0030 I2C Prescaler register                 */
    uint32 PID11; /**<  0x0034 I2C Peripheral ID register 1           */
    uint32 PID12; /**<  0x0038 I2C Peripheral ID register 2           */
    uint32 DMACR; /**<  0x003C I2C DMA Control Register               */
    uint32 rsvd7; /**<  0x0040 Reserved                               */
    uint32 rsvd8; /**<  0x0044 Reserved                               */
    uint32 PFNC;  /**<  0x0048 Pin Function Register                  */
    uint32 DIR;   /**<  0x004C Pin Direction Register                 */
    uint32 DIN;   /**<  0x0050 Pin Data In Register                   */
    uint32 DOUT;  /**<  0x0054 Pin Data Out Register                  */
    uint32 SET;   /**<  0x0058 Pin Data Set Register                  */
    uint32 CLR;   /**<  0x005C Pin Data Clr Register                  */
    uint32 PDR;   /**<  0x0060 Pin Open Drain Output Enable Register  */
    uint32 PDIS;  /**<  0x0064 Pin Pullup/Pulldown Disable Register   */
    uint32 PSEL;  /**<  0x0068 Pin Pullup/Pulldown Selection Register */
    uint32 PSRS;  /**<  0x006C Pin Slew Rate Select Register          */
} i2cBASE_t;

/** @def i2cREG1
 *   @brief I2C Register Frame Pointer
 *
 *   This pointer is used by the I2C driver to access the I2C module registers.
 */
#define i2cREG1  ( ( i2cBASE_t * ) 0xFFF7D400U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @def i2cPORT1
 *   @brief I2C GIO Port Register Pointer
 *
 *   Pointer used by the GIO driver to access I/O PORT of I2C
 *   (use the GIO drivers to access the port pins).
 */
#define i2cPORT1 ( ( gioPORT_t * ) 0xFFF7D44CU )

/* USER CODE BEGIN (2) */
/* USER CODE END */

#endif /* ifndef __REG_I2C_H__ */
