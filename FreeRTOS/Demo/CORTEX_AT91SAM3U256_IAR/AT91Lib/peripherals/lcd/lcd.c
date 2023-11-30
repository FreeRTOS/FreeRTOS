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

#include <board.h>

#if defined (AT91C_ID_LCDC)

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include "lcd.h"
#include <utility/assert.h>
#include <utility/trace.h>


//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Enables the LCD controller, after waiting for the specified number of
/// frames.
/// \param frames  Number of frames before the LCD is enabled.
//------------------------------------------------------------------------------
void LCD_Enable(unsigned int frames)
{
    TRACE_DEBUG("LCD enable\n\r");
    ASSERT((frames & 0xFFFFFF80) == 0,
           "LCD_Enable: Wrong frames value.\n\r");
    if( (AT91C_BASE_LCDC->LCDC_PWRCON & AT91C_LCDC_BUSY) == AT91C_LCDC_BUSY ) {
        TRACE_DEBUG("LCD BUSY E\n\r");
    }
    AT91C_BASE_LCDC->LCDC_PWRCON = AT91C_LCDC_PWR | (frames << 1);
}

//------------------------------------------------------------------------------
/// Disables the LCD controller, after waiting for the specified number of
/// frames.
/// \param frames  Number of frames before the LCD is shut down.
//------------------------------------------------------------------------------
void LCD_Disable(unsigned int frames)
{
    TRACE_DEBUG("LCD disable\n\r");
    ASSERT((frames & 0xFFFFFF80) == 0,
           "LCD_Disable: Wrong frames value.\n\r");
    // Remove AT91C_LCDC_PWR
    AT91C_BASE_LCDC->LCDC_PWRCON = frames << 1;
    // wait LCDC Core is in idle state
    while( (AT91C_BASE_LCDC->LCDC_PWRCON & AT91C_LCDC_BUSY) == AT91C_LCDC_BUSY ) {
    }
    TRACE_DEBUG("LCD is in IDLE state\n\r");
}

//------------------------------------------------------------------------------
/// Enables the DMA of the LCD controller.
//------------------------------------------------------------------------------
void LCD_EnableDma(void)
{
    if( (AT91C_BASE_LCDC->LCDC_DMACON & AT91C_LCDC_DMABUSY) == AT91C_LCDC_DMABUSY ) {
        TRACE_DEBUG("LCD DMA BUSY E\n\r");
    }
    AT91C_BASE_LCDC->LCDC_DMACON = AT91C_LCDC_DMAEN;
}

//------------------------------------------------------------------------------
/// Disables the DMA of the LCD controller.
//------------------------------------------------------------------------------
void LCD_DisableDma(void)
{
    AT91C_BASE_LCDC->LCDC_DMACON = 0;
    // wait LCDC DMA is in idle state
    while( (AT91C_BASE_LCDC->LCDC_DMACON & AT91C_LCDC_DMABUSY) == AT91C_LCDC_DMABUSY ) {
    }
    TRACE_DEBUG("LCD DMA is in IDLE state\n\r");
}

//------------------------------------------------------------------------------
/// Enables the selected LDC interrupt sources.
/// \param sources  Interrupt sources to enable.
//------------------------------------------------------------------------------
void LCD_EnableInterrupts(unsigned int sources)
{
    AT91C_BASE_LCDC->LCDC_IER = sources;
}

//------------------------------------------------------------------------------
/// Configures the internal clock of the LCD controller given the master clock of
/// the system and the desired pixel clock in MHz.
/// \param masterClock  Master clock frequency.
/// \param pixelClock  Pixel clock frequency.
//------------------------------------------------------------------------------
void LCD_SetPixelClock(unsigned int masterClock, unsigned int pixelClock)
{
    AT91C_BASE_LCDC->LCDC_LCDCON1 = ((masterClock / 2 / pixelClock) - 2) << 12;
}

//------------------------------------------------------------------------------
/// DMA reset
//------------------------------------------------------------------------------
void LCD_DMAReset(void)
{
    // DMA Module should be reset only when disabled and in idle state
    if( AT91C_LCDC_DMABUSY == (AT91C_BASE_LCDC->LCDC_DMACON & AT91C_LCDC_DMABUSY)) {
        TRACE_ERROR("LCD BUSY so NO DMA RESET\n\r");
    }
    if( AT91C_LCDC_DMAEN == (AT91C_BASE_LCDC->LCDC_DMACON & AT91C_LCDC_DMAEN)) {
        TRACE_ERROR("DMA Enabled, so NO DMA RESET\n\r");
    }
    AT91C_BASE_LCDC->LCDC_DMACON = AT91C_LCDC_DMARST;
}

//------------------------------------------------------------------------------
/// Sets the type of display used with the LCD controller.
/// \param displayType  Type of display used.
//------------------------------------------------------------------------------
void LCD_SetDisplayType(unsigned int displayType)
{
    unsigned int value;

    ASSERT((displayType & ~AT91C_LCDC_DISTYPE) == 0,
           "LCD_SetDisplayType: Wrong display type value.\n\r");

    value = AT91C_BASE_LCDC->LCDC_LCDCON2;
    value &= ~AT91C_LCDC_DISTYPE;
    value |= displayType;
    AT91C_BASE_LCDC->LCDC_LCDCON2 = value;
}

//------------------------------------------------------------------------------
/// Sets the scan mode used by the LCD (either single scan or double-scan).
/// \param scanMode  Scan mode to use.
//------------------------------------------------------------------------------
void LCD_SetScanMode(unsigned int scanMode)
{
    unsigned int value;

    ASSERT((scanMode & ~AT91C_LCDC_SCANMOD) == 0,
           "LCD_SetScanMode: Wrong scan mode value.\n\r");

    value = AT91C_BASE_LCDC->LCDC_LCDCON2;
    value &= ~AT91C_LCDC_SCANMOD;
    value |= scanMode;
    AT91C_BASE_LCDC->LCDC_LCDCON2 = value;
}

//------------------------------------------------------------------------------
/// Sets the number of bits per pixel used by the LCD display.
/// \param bitsPerPixel  Number of bits per pixel to use.
//------------------------------------------------------------------------------
void LCD_SetBitsPerPixel(unsigned int bitsPerPixel)
{
    unsigned int value;

    ASSERT((bitsPerPixel & ~AT91C_LCDC_PIXELSIZE) == 0,
           "LCD_SetScanMode: Wrong bitsPerPixel value.\n\r");

    value = AT91C_BASE_LCDC->LCDC_LCDCON2;
    value &= ~AT91C_LCDC_PIXELSIZE;
    value |= bitsPerPixel;
    AT91C_BASE_LCDC->LCDC_LCDCON2 = value;
}

//------------------------------------------------------------------------------
/// Sets the LCDD, LCDVSYNC, LCDHSYNC, LCDDOTCLK and LCDDEN signal polarities.
/// \param lcdd  LCDD signal polarity.
/// \param lcdvsync  LCDVSYNC signal polarity.
/// \param lcdhsync  LCDHSYNC signal polarity.
/// \param lcddotclk  LCDDOTCLK signal polarity.
/// \param lcdden  LCDDEN signal polarity.
//------------------------------------------------------------------------------
void LCD_SetPolarities(
    unsigned int lcdd,
    unsigned int lcdvsync,
    unsigned int lcdhsync,
    unsigned int lcddotclk,
    unsigned int lcdden)
{
    unsigned int value;

    ASSERT((lcdd & ~AT91C_LCDC_INVVD) == 0,
           "LCD_SetPolarities: Wrong lcdd value.\n\r");
    ASSERT((lcdvsync & ~AT91C_LCDC_INVFRAME) == 0,
           "LCD_SetPolarities: Wrong lcdvsync value.\n\r");
    ASSERT((lcdhsync & ~AT91C_LCDC_INVLINE) == 0,
           "LCD_SetPolarities: Wrong lcdhsync value.\n\r");
    ASSERT((lcddotclk & ~AT91C_LCDC_INVCLK) == 0,
           "LCD_SetPolarities: Wrong lcddotclk value.\n\r");
    ASSERT((lcdden & ~AT91C_LCDC_INVDVAL) == 0,
           "LCD_SetPolarities: Wrong lcdden value.\n\r");

    value = AT91C_BASE_LCDC->LCDC_LCDCON2;
    value &= 0xFFFFE0FF;
    value |= lcdd | lcdvsync | lcdhsync | lcddotclk | lcdden;
    AT91C_BASE_LCDC->LCDC_LCDCON2 = value;
}

//------------------------------------------------------------------------------
/// Sets the LCD clock mode, i.e. always active or active only during display
/// period.
/// \param clockMode  Clock mode to use.
//------------------------------------------------------------------------------
void LCD_SetClockMode(unsigned int clockMode)
{
    unsigned int value;

    ASSERT((clockMode & ~AT91C_LCDC_CLKMOD) == 0,
           "LCD_SetScanMode: Wrong scan mode value.\n\r");

    value = AT91C_BASE_LCDC->LCDC_LCDCON2;
    value &= ~AT91C_LCDC_CLKMOD;
    value |= clockMode;
    AT91C_BASE_LCDC->LCDC_LCDCON2 = value;
}

//------------------------------------------------------------------------------
/// Sets the format of the frame buffer memory.
/// \param format  Memory ordering format.
//------------------------------------------------------------------------------
void LCD_SetMemoryFormat(unsigned int format)
{
    unsigned int value;

    ASSERT((format & ~AT91C_LCDC_MEMOR) == 0,
           "LCD_SetMemoryFormat: Wrong memory format value.\n\r");

    value = AT91C_BASE_LCDC->LCDC_LCDCON2;
    value &= ~AT91C_LCDC_MEMOR;
    value |= format;
    AT91C_BASE_LCDC->LCDC_LCDCON2 = value;
}

//------------------------------------------------------------------------------
/// Sets the size in pixel of the LCD display.
/// \param width  Width in pixel of the LCD display.
/// \param height  Height in pixel of the LCD display.
//------------------------------------------------------------------------------
void LCD_SetSize(unsigned int width, unsigned int height)
{
    ASSERT(((width - 1) & 0xFFFFF800) == 0,
           "LCD_SetSize: Wrong width value.\n\r");
    ASSERT(((height - 1) & 0xFFFFF800) == 0,
           "LCD_SetSize: Wrong height value.\n\r");

    AT91C_BASE_LCDC->LCDC_LCDFRCFG = ((width - 1) << 21) | (height - 1);
}

//------------------------------------------------------------------------------
/// Sets the vertical timings of the LCD controller. Only meaningful when
/// using a TFT display.
/// \param vfp  Number of idle lines at the end of a frame.
/// \param vbp  Number of idle lines at the beginning of a frame.
/// \param vpw  Vertical synchronization pulse width in number of lines.
/// \param vhdly  Delay between LCDVSYNC edge and LCDHSYNC rising edge, in
///               LCDDOTCLK cycles.
//------------------------------------------------------------------------------
void LCD_SetVerticalTimings(
    unsigned int vfp,
    unsigned int vbp,
    unsigned int vpw,
    unsigned int vhdly)
{
    ASSERT((vfp & 0xFFFFFF00) == 0,
           "LCD_SetVerticalTimings: Wrong vfp value.\n\r");
    ASSERT((vbp & 0xFFFFFF00) == 0,
           "LCD_SetVerticalTimings: Wrong vbp value.\n\r");
    ASSERT(((vpw-1) & 0xFFFFFFC0) == 0,
           "LCD_SetVerticalTimings: Wrong vpw value.\n\r");
    ASSERT(((vhdly-1) & 0xFFFFFFF0) == 0,
           "LCD_SetVerticalTimings: Wrong vhdly value.\n\r");

    AT91C_BASE_LCDC->LCDC_TIM1 = vfp
                                 | (vbp << 8)
                                 | ((vpw-1) << 16)
                                 | ((vhdly-1) << 24);
}

//------------------------------------------------------------------------------
/// Sets the horizontal timings of the LCD controller. Meaningful for both
/// STN and TFT displays.
/// \param hbp  Number of idle LCDDOTCLK cycles at the beginning of a line.
/// \param hpw  Width of the LCDHSYNC pulse, in LCDDOTCLK cycles.
/// \param hfp  Number of idel LCDDOTCLK cycles at the end of a line.
//------------------------------------------------------------------------------
void LCD_SetHorizontalTimings(
    unsigned int hbp,
    unsigned int hpw,
    unsigned int hfp)
{
    ASSERT(((hbp-1) & 0xFFFFFF00) == 0,
           "LCD_SetHorizontalTimings: Wrong hbp value.\n\r");
    ASSERT(((hpw-1) & 0xFFFFFFC0) == 0,
           "LCD_SetHorizontalTimings: Wrong hpw value.\n\r");
    ASSERT(((hfp-1) & 0xFFFFFF00) == 0,
           "LCD_SetHorizontalTimings: Wrong hfp value.\n\r");

    AT91C_BASE_LCDC->LCDC_TIM2 = (hbp-1) | ((hpw-1) << 8) | ((hfp-1) << 24);
}

//------------------------------------------------------------------------------
/// Sets the address of the frame buffer in the LCD controller DMA. When using
/// dual-scan mode, this is the upper frame buffer.
/// \param address  Frame buffer address.
//------------------------------------------------------------------------------
void* LCD_SetFrameBufferAddress(void *address)
{
    void *pOldBuffer;
    
    pOldBuffer = (void *) AT91C_BASE_LCDC->LCDC_BA1;
    AT91C_BASE_LCDC->LCDC_BA1 = (unsigned int) address;
    
    return pOldBuffer;
}

//------------------------------------------------------------------------------
/// Sets the size in pixels of a frame (height * width * bpp).
/// \param frameSize  Size of frame in pixels.
//------------------------------------------------------------------------------
void LCD_SetFrameSize(unsigned int frameSize)
{
    ASSERT((frameSize & 0xFF800000) == 0,
           "LCD_SetFrameSize: Wrong frameSize value.\n\r");

    AT91C_BASE_LCDC->LCDC_FRMCFG = (frameSize& AT91C_LCDC_FRSIZE)
                                 | (AT91C_BASE_LCDC->LCDC_FRMCFG & AT91C_LCDC_BLENGTH);
}

//------------------------------------------------------------------------------
/// Sets the DMA controller burst length.
/// \param burstLength  Desired burst length.
//------------------------------------------------------------------------------
void LCD_SetBurstLength(unsigned int burstLength)
{
    ASSERT(((burstLength-1) & 0xFFFFFF80) == 0,
           "LCD_SetBurstLength: Wrong burstLength value.\n\r");

    AT91C_BASE_LCDC->LCDC_FRMCFG &= ~AT91C_LCDC_BLENGTH;
    AT91C_BASE_LCDC->LCDC_FRMCFG |= (((burstLength-1) << 24) & AT91C_LCDC_BLENGTH);

    AT91C_BASE_LCDC->LCDC_FIFO = (2048 - (2 * burstLength + 3)) & AT91C_LCDC_FIFOTH;
}

//------------------------------------------------------------------------------
/// Sets the prescaler value of the contrast control PWM.
/// \param prescaler  Desired prescaler value.
//------------------------------------------------------------------------------
void LCD_SetContrastPrescaler(unsigned int prescaler)
{
    ASSERT((prescaler & ~AT91C_LCDC_PS) == 0,
           "LCD_SetContrastPrescaler: Wrong prescaler value\n\r");

    AT91C_BASE_LCDC->LCDC_CTRSTCON &= ~AT91C_LCDC_PS;
    AT91C_BASE_LCDC->LCDC_CTRSTCON |= prescaler;
}

//------------------------------------------------------------------------------
/// Sets the polarity of the contrast PWM.
/// \param polarity  PWM polarity
//------------------------------------------------------------------------------
void LCD_SetContrastPolarity(unsigned int polarity)
{
    ASSERT((polarity & ~AT91C_LCDC_POL) == 0,
           "LCD_SetContrastPolarity: Wrong polarity value\n\r");

    AT91C_BASE_LCDC->LCDC_CTRSTCON &= ~AT91C_LCDC_POL;
    AT91C_BASE_LCDC->LCDC_CTRSTCON |= polarity;
}

//------------------------------------------------------------------------------
/// Sets the threshold value of the constrast PWM.
/// \param value  PWM threshold value.
//------------------------------------------------------------------------------
void LCD_SetContrastValue(unsigned int value)
{
    ASSERT((value & ~AT91C_LCDC_CVAL) == 0,
           "LCD_SetContrastValue: Wrong value.\n\r");

    AT91C_BASE_LCDC->LCDC_CTRSTVAL = value;
}

//------------------------------------------------------------------------------
/// Enables the contrast PWM generator.
//------------------------------------------------------------------------------
void LCD_EnableContrast(void)
{
    AT91C_BASE_LCDC->LCDC_CTRSTCON |= AT91C_LCDC_ENA_PWMGEMENABLED;
}

//------------------------------------------------------------------------------
/// Decode the RGB file
/// \param file  Buffer which holds the RGB file.
/// \param bufferLCD  Buffer in which to store the decoded image adapted to LCD.
/// \param width  Buffer width in pixels.
/// \param height  Buffer height in pixels.
/// \param bpp  Number of bits per pixels that the buffer stores.
//------------------------------------------------------------------------------
void LCD_DecodeRGB(
    unsigned char *file,
    unsigned char *bufferLCD,
    unsigned int width,
    unsigned int height,
    unsigned char bpp)
{
    unsigned int offsetLine=0, offsetLCD=0;
    unsigned int offset=1;

    while( offset < (BOARD_LCD_HEIGHT)) {
        //TRACE_DEBUG("LCD:%d LINE:%d off:%d\n\r", offsetLCD,  offsetLine, offset);
        if( width < BOARD_LCD_WIDTH ) {
            //TRACE_DEBUG("width < BOARD_LCD_WIDTH\n\r");
            while( offsetLine < (width*offset*(bpp/8)) ) {
                bufferLCD[offsetLCD] = file[offsetLine];
                offsetLine++;
                offsetLCD++;
            }
            //TRACE_DEBUG("add white\n\r");
            while( offsetLCD < (BOARD_LCD_WIDTH*offset*(bpp/8)) ) {
                bufferLCD[offsetLCD] = 0;
                //offsetLine++;
                offsetLCD++;
            }
        }
        else {
            //TRACE_DEBUG(">");
            while( offsetLCD < (BOARD_LCD_WIDTH*offset*(bpp/8)) ) {
                bufferLCD[offsetLCD] = file[offsetLine];
                offsetLine++;
                offsetLCD++;
            }
            //TRACE_DEBUG("r ");
            while( offsetLine < (width*offset*(bpp/8)) ) {
                offsetLine++;
            }            
        }
        offset++;
    }        
}

#endif

