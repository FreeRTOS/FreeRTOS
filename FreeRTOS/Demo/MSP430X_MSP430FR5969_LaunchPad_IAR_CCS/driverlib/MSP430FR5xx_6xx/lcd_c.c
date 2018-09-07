/* --COPYRIGHT--,BSD
 * Copyright (c) 2014, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * --/COPYRIGHT--*/
//*****************************************************************************
//
// lcd_c.c - Driver for the lcd_c Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup lcd_c_api lcd_c
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_LCD_C__
#include "lcd_c.h"

#include <assert.h>

//*****************************************************************************
//
// Initialization parameter instance
//
//*****************************************************************************
const LCD_C_initParam LCD_C_INIT_PARAM = {
    LCD_C_CLOCKSOURCE_ACLK,
    LCD_C_CLOCKDIVIDER_1,
    LCD_C_CLOCKPRESCALAR_1,
    LCD_C_STATIC,
    LCD_C_STANDARD_WAVEFORMS,
    LCD_C_SEGMENTS_DISABLED
};

static void setLCDFunction(uint16_t baseAddress,
                           uint8_t index,
                           uint16_t value)
{
    switch(index)
    {
    case 0:
        HWREG16(baseAddress + OFS_LCDCPCTL0) |= value;
        break;
    case 1:
        HWREG16(baseAddress + OFS_LCDCPCTL1) |= value;
        break;
    case 2:
        HWREG16(baseAddress + OFS_LCDCPCTL2) |= value;
        break;
    case 3:
        HWREG16(baseAddress + OFS_LCDCPCTL3) |= value;
        break;
    default: break;
    }
}

void LCD_C_init(uint16_t baseAddress,
                LCD_C_initParam *initParams)
{
    HWREG16(baseAddress + OFS_LCDCCTL0) &= ~LCDON;
    HWREG16(baseAddress + OFS_LCDCCTL0) &= ~(LCDMX0 | LCDMX1 | LCDMX2 | LCDSSEL
                                             | LCDLP | LCDSON | LCDDIV_31);

    HWREG16(baseAddress + OFS_LCDCCTL0) |= initParams->muxRate;
    HWREG16(baseAddress + OFS_LCDCCTL0) |= initParams->clockSource;
    HWREG16(baseAddress + OFS_LCDCCTL0) |= initParams->waveforms;
    HWREG16(baseAddress + OFS_LCDCCTL0) |= initParams->segments;
    HWREG16(baseAddress + OFS_LCDCCTL0) |= initParams->clockDivider;
    HWREG16(baseAddress + OFS_LCDCCTL0) |= initParams->clockPrescalar;
}

void LCD_C_on(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_LCDCCTL0) |= LCDON;
}

void LCD_C_off(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_LCDCCTL0) &= ~LCDON;
}

void LCD_C_clearInterrupt(uint16_t baseAddress,
                          uint16_t mask)
{
    HWREG8(baseAddress + OFS_LCDCCTL1_L) &= ~(mask >> 8);
}

uint16_t LCD_C_getInterruptStatus(uint16_t baseAddress,
                                  uint16_t mask)
{
    return (HWREG8(baseAddress + OFS_LCDCCTL1_L) & (mask >> 8));
}

void LCD_C_enableInterrupt(uint16_t baseAddress,
                           uint16_t mask)
{
    HWREG16(baseAddress + OFS_LCDCCTL1) |= mask;
}

void LCD_C_disableInterrupt(uint16_t baseAddress,
                            uint16_t mask)
{
    HWREG16(baseAddress + OFS_LCDCCTL1) &= ~mask;
}

void LCD_C_clearMemory(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_LCDCMEMCTL) |= LCDCLRM;
}

void LCD_C_clearBlinkingMemory(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_LCDCMEMCTL) |= LCDCLRBM;
}

void LCD_C_selectDisplayMemory(uint16_t baseAddress,
                               uint16_t displayMemory)
{
    HWREG16(baseAddress + OFS_LCDCMEMCTL) &= ~LCDDISP;
    HWREG16(baseAddress + OFS_LCDCMEMCTL) |= displayMemory;
}

void LCD_C_setBlinkingControl(uint16_t baseAddress,
                              uint8_t clockDivider,
                              uint8_t clockPrescalar,
                              uint8_t mode)
{
    HWREG16(baseAddress +
            OFS_LCDCBLKCTL) &= ~(LCDBLKDIV0 | LCDBLKDIV1 | LCDBLKDIV2 |
                                 LCDBLKPRE0 | LCDBLKPRE1 |
                                 LCDBLKPRE2 |
                                 LCDBLKMOD0 | LCDBLKMOD1
                                 );
    HWREG16(baseAddress +
            OFS_LCDCBLKCTL) |= clockDivider | clockPrescalar | mode;
}

void LCD_C_enableChargePump(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_LCDCCTL0) &= ~LCDON;
    HWREG16(baseAddress + OFS_LCDCVCTL) |= LCDCPEN;
}

void LCD_C_disableChargePump(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_LCDCCTL0) &= ~LCDON;
    HWREG16(baseAddress + OFS_LCDCVCTL) &= ~LCDCPEN;
}

void LCD_C_selectBias(uint16_t baseAddress,
                      uint16_t bias)
{
    HWREG16(baseAddress + OFS_LCDCCTL0) &= ~LCDON;
    HWREG16(baseAddress + OFS_LCDCVCTL) &= ~LCD2B;

    HWREG16(baseAddress + OFS_LCDCVCTL) |= bias;
}

void LCD_C_selectChargePumpReference(uint16_t baseAddress,
                                     uint16_t reference)
{
    HWREG16(baseAddress + OFS_LCDCCTL0) &= ~LCDON;
    HWREG16(baseAddress + OFS_LCDCVCTL) &= ~VLCDREF_3;

    HWREG16(baseAddress + OFS_LCDCVCTL) |= reference;
}

void LCD_C_setVLCDSource(uint16_t baseAddress,
                         uint16_t vlcdSource,
                         uint16_t v2v3v4Source,
                         uint16_t v5Source)
{
    HWREG16(baseAddress + OFS_LCDCCTL0) &= ~LCDON;
    HWREG16(baseAddress + OFS_LCDCVCTL) &= ~VLCDEXT;
    HWREG16(baseAddress + OFS_LCDCVCTL) &= ~LCDREXT;
    HWREG16(baseAddress + OFS_LCDCVCTL) &= ~LCDEXTBIAS;
    HWREG16(baseAddress + OFS_LCDCVCTL) &= ~R03EXT;

    HWREG16(baseAddress + OFS_LCDCVCTL) |= vlcdSource;
    HWREG16(baseAddress + OFS_LCDCVCTL) |= v2v3v4Source;
    HWREG16(baseAddress + OFS_LCDCVCTL) |= v5Source;
}

void LCD_C_setVLCDVoltage(uint16_t baseAddress,
                          uint16_t voltage)
{
    HWREG16(baseAddress + OFS_LCDCCTL0) &= ~LCDON;
    HWREG16(baseAddress + OFS_LCDCVCTL) &= ~VLCD_15;

    HWREG16(baseAddress + OFS_LCDCVCTL) |= voltage;
}

void LCD_C_setPinAsLCDFunction(uint16_t baseAddress,
                               uint8_t pin)
{
    HWREG16(baseAddress + OFS_LCDCCTL0) &= ~LCDON;

    uint8_t idx = pin >> 4;
    uint16_t val = 1 << (pin & 0xF);

    setLCDFunction(baseAddress, idx, val);
}

void LCD_C_setPinAsPortFunction(uint16_t baseAddress,
                                uint8_t pin)
{
    HWREG16(baseAddress + OFS_LCDCCTL0) &= ~LCDON;

    uint8_t idx = pin >> 4;
    uint16_t val = 1 << (pin & 0xF);

    switch(idx)
    {
    case 0:
        HWREG16(baseAddress + OFS_LCDCPCTL0) &= ~val;
        break;
    case 1:
        HWREG16(baseAddress + OFS_LCDCPCTL1) &= ~val;
        break;
    case 2:
        HWREG16(baseAddress + OFS_LCDCPCTL2) &= ~val;
        break;
    case 3:
        HWREG16(baseAddress + OFS_LCDCPCTL3) &= ~val;
        break;
    default: break;
    }
}

void LCD_C_setPinAsLCDFunctionEx(uint16_t baseAddress,
                                 uint8_t startPin,
                                 uint8_t endPin)
{
    uint8_t startIdx = startPin >> 4;
    uint8_t endIdx = endPin >> 4;
    uint8_t startPos = startPin & 0xF;
    uint8_t endPos = endPin & 0xF;
    uint16_t val = 0;
    uint8_t i = 0;

    HWREG16(baseAddress + OFS_LCDCCTL0) &= ~LCDON;

    if(startIdx == endIdx)
    {
        val = (0xFFFF >> (15 - endPos)) & (0xFFFF << startPos);

        setLCDFunction(baseAddress, startIdx, val);
    }
    else
    {
        val = 0xFFFF >> (15 - endPos);
        setLCDFunction(baseAddress, endIdx, val);

        for(i = endIdx - 1; i > startIdx; i--)
        {
            setLCDFunction(baseAddress, i, 0xFFFF);
        }

        val = 0xFFFF << startPos;
        setLCDFunction(baseAddress, startIdx, val);
    }
}

void LCD_C_setMemory(uint16_t baseAddress,
                     uint8_t pin,
                     uint8_t value)
{
    uint8_t muxRate = HWREG16(baseAddress + OFS_LCDCCTL0)
                      & (LCDMX2 | LCDMX1 | LCDMX0);

    // static, 2-mux, 3-mux, 4-mux
    if(muxRate <= (LCDMX1 | LCDMX0))
    {
        if(pin & 1)
        {
            HWREG8(baseAddress + OFS_LCDM1 + pin / 2) &= 0x0F;
            HWREG8(baseAddress + OFS_LCDM1 + pin / 2) |= (value & 0xF) << 4;
        }
        else
        {
            HWREG8(baseAddress + OFS_LCDM1 + pin / 2) &= 0xF0;
            HWREG8(baseAddress + OFS_LCDM1 + pin / 2) |= (value & 0xF);
        }
    }
    else
    {
        //5-mux, 6-mux, 7-mux, 8-mux
        HWREG8(baseAddress + OFS_LCDM1 + pin) = value;
    }
}

void LCD_C_setBlinkingMemory(uint16_t baseAddress,
                             uint8_t pin,
                             uint8_t value)
{
    uint8_t muxRate = HWREG16(baseAddress + OFS_LCDCCTL0)
                      & (LCDMX2 | LCDMX1 | LCDMX0);

    // static, 2-mux, 3-mux, 4-mux
    if(muxRate <= (LCDMX1 | LCDMX0))
    {
        if(pin & 1)
        {
            HWREG8(baseAddress + OFS_LCDBM1 + pin / 2) &= 0x0F;
            HWREG8(baseAddress + OFS_LCDBM1 + pin / 2) |= (value & 0xF) << 4;
        }
        else
        {
            HWREG8(baseAddress + OFS_LCDBM1 + pin / 2) &= 0xF0;
            HWREG8(baseAddress + OFS_LCDBM1 + pin / 2) |= (value & 0xF);
        }
    }
    else
    {
        //5-mux, 6-mux, 7-mux, 8-mux
        HWREG8(baseAddress + OFS_LCDBM1 + pin) = value;
    }
}

void LCD_C_configChargePump(uint16_t baseAddress,
                            uint16_t syncToClock,
                            uint16_t functionControl)
{
    HWREG16(baseAddress + OFS_LCDCCPCTL) &= ~(LCDCPCLKSYNC);
    HWREG16(baseAddress + OFS_LCDCCPCTL) &= ~(LCDCPDIS7 | LCDCPDIS6 | LCDCPDIS5
                                              | LCDCPDIS4 | LCDCPDIS3 |
                                              LCDCPDIS2 | LCDCPDIS1 |
                                              LCDCPDIS0);

    HWREG16(baseAddress + OFS_LCDCCPCTL) |= syncToClock | functionControl;
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for lcd_c_api
//! @}
//
//*****************************************************************************
