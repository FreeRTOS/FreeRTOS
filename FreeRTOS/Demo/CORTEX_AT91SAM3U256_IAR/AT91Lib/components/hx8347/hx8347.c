/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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

//------------------------------------------------------------------------------
/// \unit
///
/// !Purpose
///
/// HX8347 driver
///
/// !Usage
///
/// Explanation on the usage of the code made available through the header file.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------
#include <board.h>
#include <stdio.h>

#ifdef BOARD_LCD_HX8347

#include "hx8347.h"

//------------------------------------------------------------------------------
//         Types
//------------------------------------------------------------------------------
typedef volatile unsigned short REG16;

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------
/// LCD index register address
#define LCD_IR(baseAddr) (*((REG16 *)(baseAddr)))
/// LCD status register address
#define LCD_SR(baseAddr) (*((REG16 *)(baseAddr)))
/// LCD data address
#define LCD_D(baseAddr)  (*((REG16 *)((unsigned int)(baseAddr) + BOARD_LCD_RS)))

/// HX8347 ID code
#define HX8347_HIMAXID_CODE    0x47

/// HX8347 LCD Registers
#define HX8347_R00H        0x00
#define HX8347_R01H        0x01
#define HX8347_R02H        0x02
#define HX8347_R03H        0x03
#define HX8347_R04H        0x04
#define HX8347_R05H        0x05
#define HX8347_R06H        0x06
#define HX8347_R07H        0x07
#define HX8347_R08H        0x08
#define HX8347_R09H        0x09
#define HX8347_R0AH        0x0A
#define HX8347_R0CH        0x0C
#define HX8347_R0DH        0x0D
#define HX8347_R0EH        0x0E
#define HX8347_R0FH        0x0F
#define HX8347_R10H        0x10
#define HX8347_R11H        0x11
#define HX8347_R12H        0x12
#define HX8347_R13H        0x13
#define HX8347_R14H        0x14
#define HX8347_R15H        0x15
#define HX8347_R16H        0x16
#define HX8347_R18H        0x18
#define HX8347_R19H        0x19
#define HX8347_R1AH        0x1A
#define HX8347_R1BH        0x1B
#define HX8347_R1CH        0x1C
#define HX8347_R1DH        0x1D
#define HX8347_R1EH        0x1E
#define HX8347_R1FH        0x1F
#define HX8347_R20H        0x20
#define HX8347_R21H        0x21
#define HX8347_R22H        0x22
#define HX8347_R23H        0x23
#define HX8347_R24H        0x24
#define HX8347_R25H        0x25
#define HX8347_R26H        0x26
#define HX8347_R27H        0x27
#define HX8347_R28H        0x28
#define HX8347_R29H        0x29
#define HX8347_R2AH        0x2A
#define HX8347_R2BH        0x2B
#define HX8347_R2CH        0x2C
#define HX8347_R2DH        0x2D
#define HX8347_R35H        0x35
#define HX8347_R36H        0x36
#define HX8347_R37H        0x37
#define HX8347_R38H        0x38
#define HX8347_R39H        0x39
#define HX8347_R3AH        0x3A
#define HX8347_R3BH        0x3B
#define HX8347_R3CH        0x3C
#define HX8347_R3DH        0x3D
#define HX8347_R3EH        0x3E
#define HX8347_R40H        0x40
#define HX8347_R41H        0x41
#define HX8347_R42H        0x42
#define HX8347_R43H        0x43
#define HX8347_R44H        0x44
#define HX8347_R45H        0x45
#define HX8347_R46H        0x46
#define HX8347_R47H        0x47
#define HX8347_R48H        0x48
#define HX8347_R49H        0x49
#define HX8347_R4AH        0x4A
#define HX8347_R4BH        0x4B
#define HX8347_R4CH        0x4C
#define HX8347_R4DH        0x4D
#define HX8347_R4EH        0x4E
#define HX8347_R4FH        0x4F
#define HX8347_R50H        0x50
#define HX8347_R51H        0x51
#define HX8347_R64H        0x64
#define HX8347_R65H        0x65
#define HX8347_R66H        0x66
#define HX8347_R67H        0x67
#define HX8347_R70H        0x70
#define HX8347_R72H        0x72
#define HX8347_R90H        0x90
#define HX8347_R91H        0x91
#define HX8347_R93H        0x93
#define HX8347_R94H        0x94
#define HX8347_R95H        0x95

//------------------------------------------------------------------------------
//         External functions
//------------------------------------------------------------------------------
// External delay 1 ms function
#include "FreeRTOS.h"
#include "task.h"
#define Delay(ms) vTaskDelay(ms/portTICK_PERIOD_MS)

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Write data to LCD Register.
/// \param pLcdBase   LCD base address.
/// \param reg        Register address.
/// \param data       Data to be written.
//------------------------------------------------------------------------------
void LCD_WriteReg(void *pLcdBase, unsigned char reg, unsigned short data)
{
    LCD_IR(pLcdBase) = reg;
    LCD_D(pLcdBase)  = data;
}

//------------------------------------------------------------------------------
/// Read data from LCD Register.
/// \param pLcdBase   LCD base address.
/// \param reg        Register address.
/// \return data      Data to be read.
//------------------------------------------------------------------------------
unsigned short LCD_ReadReg(void *pLcdBase, unsigned char reg)
{
    LCD_IR(pLcdBase) = reg;
    return LCD_D(pLcdBase);
}

//------------------------------------------------------------------------------
/// Read LCD status Register.
/// \param pLcdBase   LCD base address.
/// \param reg        Register address.
/// \return data      Status Data.
//------------------------------------------------------------------------------
unsigned short LCD_ReadStatus(void *pLcdBase)
{
    return LCD_SR(pLcdBase);
}

//------------------------------------------------------------------------------
/// Prepare to write GRAM data.
/// \param pLcdBase   LCD base address.
//------------------------------------------------------------------------------
void LCD_WriteRAM_Prepare(void *pLcdBase)
{
    LCD_IR(pLcdBase) = HX8347_R22H;
}

//------------------------------------------------------------------------------
/// Write data to LCD GRAM.
/// \param pLcdBase   LCD base address.
/// \param color      16-bits RGB color.
//------------------------------------------------------------------------------
void LCD_WriteRAM(void *pLcdBase, unsigned short color)
{
    // Write 16-bit GRAM Reg
    LCD_D(pLcdBase) = color;
}

//------------------------------------------------------------------------------
/// Read GRAM data.
/// \param pLcdBase   LCD base address.
/// \return           16-bits RGB color.
//------------------------------------------------------------------------------
unsigned short LCD_ReadRAM(void *pLcdBase)
{
    // Read 16-bit GRAM Reg
    return LCD_D(pLcdBase);
}

//------------------------------------------------------------------------------
/// Dump register data.
/// \param pLcdBase   LCD base address.
/// \param startAddr  Register start address.
/// \param endAddr    Register end address.
//------------------------------------------------------------------------------
void LCD_DumpReg(void *pLcdBase, unsigned char startAddr, unsigned char endAddr)
{
    unsigned short tmp;
    unsigned char addr;

    for (addr = startAddr; addr <= endAddr; addr++) {

        tmp = LCD_ReadReg(pLcdBase, addr);
        printf("LCD.r 0x%x = 0x%x\n\r", addr, tmp);
    }
}

//------------------------------------------------------------------------------
/// Initialize the LCD controller.
/// \param pLcdBase   LCD base address.
//------------------------------------------------------------------------------
void LCD_Initialize(void *pLcdBase)
{
    unsigned short chipid;

    // Check HX8347 chipid
    chipid = LCD_ReadReg(pLcdBase, HX8347_R67H);
    if(chipid != HX8347_HIMAXID_CODE) {

        printf("Read HX8347 chip ID error, skip initialization.\r\n");
        return ;
    }

    // Start internal OSC
    LCD_WriteReg(pLcdBase, HX8347_R19H, 0x49); // OSCADJ=10 0000, OSD_EN=1 //60Hz
    LCD_WriteReg(pLcdBase, HX8347_R93H, 0x0C); // RADJ=1100

    // Power on flow
    LCD_WriteReg(pLcdBase, HX8347_R44H, 0x4D); // VCM=100 1101
    LCD_WriteReg(pLcdBase, HX8347_R45H, 0x11); // VDV=1 0001
    LCD_WriteReg(pLcdBase, HX8347_R20H, 0x40); // BT=0100
    LCD_WriteReg(pLcdBase, HX8347_R1DH, 0x07); // VC1=111
    LCD_WriteReg(pLcdBase, HX8347_R1EH, 0x00); // VC3=000
    LCD_WriteReg(pLcdBase, HX8347_R1FH, 0x04); // VRH=0100

    LCD_WriteReg(pLcdBase, HX8347_R1CH, 0x04); // AP=100
    LCD_WriteReg(pLcdBase, HX8347_R1BH, 0x10); // GASENB=0, PON=1, DK=0, XDK=0, DDVDH_TRI=0, STB=0
    Delay(50);

    LCD_WriteReg(pLcdBase, HX8347_R43H, 0x80); // Set VCOMG=1
    Delay(50);

    // Gamma for CMO 2.8
    LCD_WriteReg(pLcdBase, HX8347_R46H, 0x95);
    LCD_WriteReg(pLcdBase, HX8347_R47H, 0x51);
    LCD_WriteReg(pLcdBase, HX8347_R48H, 0x00);
    LCD_WriteReg(pLcdBase, HX8347_R49H, 0x36);
    LCD_WriteReg(pLcdBase, HX8347_R4AH, 0x11);
    LCD_WriteReg(pLcdBase, HX8347_R4BH, 0x66);
    LCD_WriteReg(pLcdBase, HX8347_R4CH, 0x14);
    LCD_WriteReg(pLcdBase, HX8347_R4DH, 0x77);
    LCD_WriteReg(pLcdBase, HX8347_R4EH, 0x13);
    LCD_WriteReg(pLcdBase, HX8347_R4FH, 0x4C);
    LCD_WriteReg(pLcdBase, HX8347_R50H, 0x46);
    LCD_WriteReg(pLcdBase, HX8347_R51H, 0x46);

    //240x320 window setting
    LCD_WriteReg(pLcdBase, HX8347_R02H, 0x00); // Column address start2
    LCD_WriteReg(pLcdBase, HX8347_R03H, 0x00); // Column address start1
    LCD_WriteReg(pLcdBase, HX8347_R04H, 0x00); // Column address end2
    LCD_WriteReg(pLcdBase, HX8347_R05H, 0xEF); // Column address end1
    LCD_WriteReg(pLcdBase, HX8347_R06H, 0x00); // Row address start2
    LCD_WriteReg(pLcdBase, HX8347_R07H, 0x00); // Row address start1
    LCD_WriteReg(pLcdBase, HX8347_R08H, 0x01); // Row address end2
    LCD_WriteReg(pLcdBase, HX8347_R09H, 0x3F); // Row address end1

    // Display Setting
    LCD_WriteReg(pLcdBase, HX8347_R01H, 0x06); // IDMON=0, INVON=1, NORON=1, PTLON=0
    LCD_WriteReg(pLcdBase, HX8347_R16H, 0xC8); // MY=1, MX=1, MV=0, BGR=1
    LCD_WriteReg(pLcdBase, HX8347_R23H, 0x95); // N_DC=1001 0101
    LCD_WriteReg(pLcdBase, HX8347_R24H, 0x95); // P_DC=1001 0101
    LCD_WriteReg(pLcdBase, HX8347_R25H, 0xFF); // I_DC=1111 1111
    LCD_WriteReg(pLcdBase, HX8347_R27H, 0x06); // N_BP=0000 0110
    LCD_WriteReg(pLcdBase, HX8347_R28H, 0x06); // N_FP=0000 0110
    LCD_WriteReg(pLcdBase, HX8347_R29H, 0x06); // P_BP=0000 0110
    LCD_WriteReg(pLcdBase, HX8347_R2AH, 0x06); // P_FP=0000 0110
    LCD_WriteReg(pLcdBase, HX8347_R2CH, 0x06); // I_BP=0000 0110
    LCD_WriteReg(pLcdBase, HX8347_R2DH, 0x06); // I_FP=0000 0110
    LCD_WriteReg(pLcdBase, HX8347_R3AH, 0x01); // N_RTN=0000, N_NW=001
    LCD_WriteReg(pLcdBase, HX8347_R3BH, 0x01); // P_RTN=0000, P_NW=001
    LCD_WriteReg(pLcdBase, HX8347_R3CH, 0xF0); // I_RTN=1111, I_NW=000
    LCD_WriteReg(pLcdBase, HX8347_R3DH, 0x00); // DIV=00
    LCD_WriteReg(pLcdBase, HX8347_R3EH, 0x38); // SON=38h
    LCD_WriteReg(pLcdBase, HX8347_R40H, 0x0F); // GDON=0Fh
    LCD_WriteReg(pLcdBase, HX8347_R41H, 0xF0); // GDOF=F0h
}

//------------------------------------------------------------------------------
/// Turn on the LCD.
/// \param pLcdBase   LCD base address.
//------------------------------------------------------------------------------
void LCD_On(void *pLcdBase)
{
    // Display ON Setting
    LCD_WriteReg(pLcdBase, HX8347_R90H, 0x7F); // SAP=0111 1111
    LCD_WriteReg(pLcdBase, HX8347_R26H, 0x04); // GON=0, DTE=0, D=01
    Delay(100);
    LCD_WriteReg(pLcdBase, HX8347_R26H, 0x24); // GON=1, DTE=0, D=01
    LCD_WriteReg(pLcdBase, HX8347_R26H, 0x2C); // GON=1, DTE=0, D=11
    Delay(100);
    LCD_WriteReg(pLcdBase, HX8347_R26H, 0x3C); // GON=1, DTE=1, D=11
}

//------------------------------------------------------------------------------
/// Turn off the LCD.
/// \param pLcdBase   LCD base address.
//------------------------------------------------------------------------------
void LCD_Off(void *pLcdBase)
{
    LCD_WriteReg(pLcdBase, HX8347_R90H, 0x00); // SAP=0000 0000
    LCD_WriteReg(pLcdBase, HX8347_R26H, 0x00); // GON=0, DTE=0, D=00
}

//------------------------------------------------------------------------------
/// Set cursor of LCD srceen.
/// \param pLcdBase   LCD base address.
/// \param x          X-coordinate of upper-left corner on LCD.
/// \param y          Y-coordinate of upper-left corner on LCD.
//------------------------------------------------------------------------------
void LCD_SetCursor(void *pLcdBase, unsigned short x, unsigned short y)
{
    unsigned char x1, x2, y1, y2;

    x1 = x & 0xff;
    x2 = (x & 0xff00) >>8;
    y1 = y & 0xff;
    y2 = (y & 0xff00) >>8;
    LCD_WriteReg(pLcdBase, HX8347_R02H, x2); // column high
    LCD_WriteReg(pLcdBase, HX8347_R03H, x1); // column low
    LCD_WriteReg(pLcdBase, HX8347_R06H, y2); // row high
    LCD_WriteReg(pLcdBase, HX8347_R07H, y1); // row low
}
#endif //#ifdef BOARD_LCD_HX8347
