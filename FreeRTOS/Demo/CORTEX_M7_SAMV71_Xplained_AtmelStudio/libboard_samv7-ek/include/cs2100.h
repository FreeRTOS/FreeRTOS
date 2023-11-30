/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
  * \file
  *
  * Implementation WM8904 driver.
  *
  */

#ifndef CS2100_H
#define CS2100_H

#include "board.h"

/*----------------------------------------------------------------------------
 *         Definitions
 *----------------------------------------------------------------------------*/

#define CS2100_SLAVE_ADDRESS                    0x4E

/** ID and Rev register*/
#define CS2100_REG_ID                           0x01

/** VMID control 0 register*/
#define CS2100_REG_CTRL                         0x02

/** MIC Bias control 0 register*/
#define CS2100_REG_DEV_CFG1                     0x03

/** Bias control 1 register*/
#define CS2100_REG_CFG                          0x05

/** Power management control 0 register*/
#define CS2100_REG_32_BIT_RATIO_1               0x06
/** Power management control 0 register*/
#define CS2100_REG_32_BIT_RATIO_2               0x07
/** Power management control 0 register*/
#define CS2100_REG_32_BIT_RATIO_3               0x08
/** Power management control 0 register*/
#define CS2100_REG_32_BIT_RATIO_4               0x09
/** Power management control 2 register*/
#define CS2100_REG_FUNC_CFG1                    0x16
/** Power management control 3 register*/
#define CS2100_REG_FUNC_CFG2                    0x17
/** Power management control 3 register*/
#define CS2100_REG_FUNC_CFG3                    0x1E

/*----------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/

extern uint16_t CS2100_Read(
				Twid *pTwid,
				uint32_t device, 
				uint32_t regAddr);

extern void CS2100_Write(
				Twid *pTwid, 
				uint32_t device,
				uint32_t regAddr, 
				uint16_t data);

extern uint8_t CS2100_Init(Twid *pTwid, uint32_t device, uint32_t PCK);
#endif // CS2100_H


