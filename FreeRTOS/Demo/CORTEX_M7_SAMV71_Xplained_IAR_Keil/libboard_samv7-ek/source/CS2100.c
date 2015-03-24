/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

/*----------------------------------------------------------------------------
 *        Type
 *----------------------------------------------------------------------------*/
typedef struct {
    uint16_t value;
    uint8_t address;
}CS2100_PARA;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Read data from CS2100 Register.
 *
 * \param pTwid   Pointer to twi driver structure
 * \param device  Twi slave address.
 * \param regAddr Register address to read.
 * \return value in the given register.
 */
uint16_t CS2100_Read(Twid *pTwid,
                     uint32_t device,
                     uint32_t regAddr)
{
    uint16_t bitsDataRegister;
    uint8_t Tdata[2]={0,0};

    TWID_Read(pTwid, device, regAddr, 1, Tdata, 2, 0);
    bitsDataRegister = (Tdata[0] << 8) | Tdata[1];
    return bitsDataRegister;
}

/**
 * \brief  Write data to WM8904 Register.
 *
 * \param pTwid   Pointer to twi driver structure
 * \param device  Twi slave address.
 * \param regAddr Register address to read.
 * \param data    Data to write
 */
void CS2100_Write(Twid *pTwid,
                  uint32_t device,
                  uint32_t regAddr,
                  uint16_t data)
{
    uint8_t tmpData[2];
    
    tmpData[0] = (data & 0xff00) >> 8;
    tmpData[1] = data & 0xff;
    TWID_Write(pTwid, device, regAddr, 1, tmpData, 2, 0);
}

uint8_t CS2100_Init(Twid *pTwid, uint32_t device,  uint32_t PCK)
{
    uint16_t data = 0;

    // Reset (write Reg@0x0 to reset)
    CS2100_Write(pTwid, device, 0, 0xFFFF);

    for(data=0;data<1000;data++);
    //wait ready    
    while(data!=0x8904)
        data=CS2100_Read(pTwid, device, 0);

    

    
    return 0;
}


